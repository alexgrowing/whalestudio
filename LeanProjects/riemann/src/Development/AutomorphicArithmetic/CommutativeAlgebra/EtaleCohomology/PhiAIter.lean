import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiAZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TorsionOfVec
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NatCastQb
import Development.AutomorphicArithmetic.EtaleIdempotents.GaloisEquivariantTensorDescentOfPrimePowerUnits
import Development.AutomorphicArithmetic.EtaleIdempotents.IntegersResidueEqZeroOfNotIsUnit
import Development.AutomorphicArithmetic.EtaleIdempotents.CrisFrobeniusIterateEvalEtaleFamily
import Development.AutomorphicArithmetic.EtaleIdempotents.GaloisActionEvalEtaleFamilyExistsDenominator
import Development.AutomorphicArithmetic.EtaleIdempotents.EvalEtaleFamilyMemLimitOfReduced
import Development.AutomorphicArithmetic.EtaleIdempotents.IntegersResidueEqThetaCoeffPowOfTeichmuller

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private theorem gRes_pow (r : Res l K) (f : ℕ) (hk : ∀ x : r.k, x ^ l ^ f = x) (x : OK l K) : gRes r x ^ l ^ f = gRes r x := by
  change (Ideal.Quotient.mk _) (r.s (r.ρ x)) ^ l ^ f = (Ideal.Quotient.mk _) (r.s (r.ρ x))
  rw [← map_pow, ← map_pow, hk]

private theorem galA_tA (g : K.fixingSubgroup) : ∃ χ : ℤ_[l]ˣ, galA g (tA l) = zA l χ * tA l :=
  ⟨cycloChar K (IntermediateField.fixingSubgroupEquiv K g), by
    have := ACris.gal_smul_periodT (K := K) (IntermediateField.fixingSubgroupEquiv K g) (untilt_epsilon (p := l))
    rwa [ACris.gal_smul_def] at this⟩

private theorem phiA_tA : phiA l (tA l) = (l : Acris l) * tA l := ACris.phi_periodT_eq_mul _

private theorem phiA_zA (x : ℤ_[l]) : phiA l (zA l x) = zA l x := by
  change ACris.phi ℂ_[l] l (algebraMap (Ainf l) (Acris l) (IsPerfectoidField.padicIntToWitt l x)) = _
  rw [ACris.phi_algebraMap, ACris.frobenius_padicIntToWitt]
  rfl

private theorem aux_sub {R Mo : Type*} [CommRing R] [AddCommGroup Mo] [Module R Mo] (A X t : R) (u s : ℕ) (G E : Mo)
    (h : A • G = (A * X ^ s) • E) : A • ((X * t) ^ u • G) - (A * X ^ (u + s)) • (t ^ u • E) = 0 := by
  rw [smul_comm A, h, smul_smul, smul_smul, ← sub_smul]
  convert zero_smul R E using 2
  ring

private theorem iter_smul_gen {R Mo : Type*} [SMul R Mo] (φ : R → R) (ϕ : Mo → Mo)
    (h : ∀ (a : R) (x : Mo), ϕ (a • x) = φ a • ϕ x) (N : ℕ) (a : R) (x : Mo) :
    ϕ^[N] (a • x) = (φ^[N] a) • ϕ^[N] x := by
  induction N generalizing a x with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, h, ih, Function.iterate_succ_apply, Function.iterate_succ_apply]

private theorem phi_iter_smul (P : PAlg l ⥤ Type) (n j N : ℕ) (a : Acris l) (x : MH P n j) :
    (phiH P n j)^[N] (a • x) = ((phiA l)^[N] a) • (phiH P n j)^[N] x :=
  iter_smul_gen (phiA l) (phiH P n j) (fun a x => LinearMap.map_smulₛₗ ((phiMor P n).pull j) a x) N a x

private theorem phiA_iter_l (N : ℕ) : (phiA l)^[N] (l : Acris l) = l := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', ih, map_natCast]

private theorem phiA_iterate_tA (N : ℕ) : (phiA l)^[N] (tA l) = (l : Acris l) ^ N * tA l := by
  induction N with
  | zero => simp
  | succ N ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, phiA_tA]; ring

private theorem phiA_iterate_zA (N : ℕ) (x : ℤ_[l]) : (phiA l)^[N] (zA l x) = zA l x := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', ih, phiA_zA]

private theorem chain1 {R Q H Γ : Type*} {Mn : ℕ → Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup H] [Module R H]
    [∀ n, AddCommGroup (Mn n)] [∀ n, Module R (Mn n)] (l : ℕ) (t : R) (φ : R →+* R) (σ : Γ → R →+* R) (X : Γ → R)
    (b : ∀ n, H →ₗ[R] Mn n) (G : Γ → H → H) (γ : ∀ g n, Mn n →ₛₗ[σ g] Mn n) (u s N : ℕ) (α : H →+ Q) (T : Γ → Q →+ Q)
    (hker : ∀ x, (∀ n, b n x = 0) → t ^ u • x = 0) (hgal : ∀ g x n, b n (G g x) = γ g n (b n x))
    (E : ∀ n, Mn n) (h : H) (hh : ∀ n, b n h = t ^ u • E n) (hχ : ∀ g, σ g t = X g * t)
    (hl : φ^[N] (l : R) = l) (ht : φ^[N] t = (l : R) ^ N * t) (hX : ∀ g, φ^[N] (X g) = X g)
    (lin : ∀ (a : R) x, α (a • x) = (φ^[N] a) • α x) (gal : ∀ g x, α (G g x) = T g (α x))
    (hab : ∀ g, ∃ a b' : ℕ, ∀ n, ((l : R) ^ a * t ^ b') • γ g n (E n) = ((l : R) ^ a * t ^ b' * X g ^ s) • E n) (g : Γ) :
    ∃ a b' : ℕ, ((l : R) ^ a * t ^ b') • T g (α h) = ((l : R) ^ a * t ^ b' * X g ^ (u + s)) • α h := by
  obtain ⟨a, c, hac⟩ := hab g
  have h0 := hker (((l : R) ^ a * t ^ c) • G g h - ((l : R) ^ a * t ^ c * X g ^ (u + s)) • h) fun n => by
    rw [map_sub, map_smul, map_smul, hgal, hh]
    have e2 : γ g n (t ^ u • E n) = (X g * t) ^ u • γ g n (E n) := by
      rw [← hχ g, LinearMap.map_smulₛₗ, map_pow]
    rw [e2]
    exact aux_sub _ _ _ _ _ _ _ (hac n)
  rw [smul_sub, smul_smul, smul_smul, sub_eq_zero] at h0
  have h1 := congrArg α h0
  rw [lin, lin, gal] at h1
  have it : ∀ (x y : R), φ^[N] (x * y) = φ^[N] x * φ^[N] y := fun x y => iterate_map_mul φ N x y
  have ip : ∀ (x : R) (k : ℕ), φ^[N] (x ^ k) = (φ^[N] x) ^ k := fun x k => iterate_map_pow φ N x k
  simp only [it, ip, hl, ht, hX] at h1
  refine ⟨a + N * (c + u), c + u, ?_⟩
  convert h1 using 2 <;> ring

private theorem chain2 {R Q H : Type*} {Mn : ℕ → Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup H] [Module R H]
    [∀ n, AddCommGroup (Mn n)] [∀ n, Module R (Mn n)] (l : ℕ) (t : R) (φ : R →+* R)
    (b : ∀ n, H →ₗ[R] Mn n) (P : H → H) (ϕ : ∀ n, Mn n → Mn n) (u r N e a' b' : ℕ) (α : H → Q) (β : Q →ₗ[R] H) (h : H) (q : Q)
    (E E' : ∀ n, Mn n) (hh : ∀ n, b n h = t ^ u • E n) (hl : φ^[N] (l : R) = l) (ht : φ^[N] t = (l : R) ^ N * t)
    (hy : ((l : R) ^ a' * t ^ b') • α h = t ^ (b' + (u + r)) • q) (fac : β (α h) = (l : R) ^ e • P^[N] h)
    (hphi : ∀ x n, b n (P x) = ϕ n (b n x)) (hit : ∀ n (a : R) x, (ϕ n)^[N] (a • x) = (φ^[N] a) • (ϕ n)^[N] x)
    (hE : ∀ n, (ϕ n)^[N] (E n) = E' n) (n : ℕ) :
    ((l : R) ^ (a' + e + N * u) * t ^ (b' + u)) • E' n = t ^ (b' + u + r) • b n (β q) := by
  have hP : ∀ (k : ℕ) x, b n (P^[k] x) = (ϕ n)^[k] (b n x) := fun k => by
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hphi, ih]
  have h1 := congrArg (fun x => b n (β x)) hy
  simp only [map_smul, fac, smul_smul, hP, hh, hit, hE] at h1
  have ip : ∀ (x : R) (k : ℕ), φ^[N] (x ^ k) = (φ^[N] x) ^ k := fun x k => iterate_map_pow φ N x k
  simp only [ip, ht, smul_smul] at h1
  have e1 : t ^ (b' + u + r) = t ^ (b' + (u + r)) := by rw [add_assoc]
  rw [e1, ← h1]
  congr 1
  ring

private theorem keyStep {r : Res l K} {M : Model l K} {f N j : ℕ} (hk : ∀ x : r.k, x ^ l ^ f = x)
    {Fr : PQ M.p (gRes r) ⟶ PQ M.p (gRes r)} {ρ : M.P ⟶ PQ M.p (gRes r)} (hFr : IsFr f Fr) (hρ : IsRd N ρ)
    (F : Pb.Fac r N) (hPin : Pin F M j) (y : Pb.LW r M j) (n : ℕ) :
    ∃ x : MH (PQ M.p (gRes r)) n j, (phiH _ n j)^[f] x = pullH Fr n j x ∧
      betaM M n j (levH (F.β M j ((1 : Pb.AW r) ⊗ₜ y)) n) = pullH ρ n j x :=
  Exists.elim (hPin n) fun m hm =>
    Exists.elim (absCl l K r M f N n j hk Fr ρ hFr hρ m hm.1 (y.1 n)) fun x hx =>
      ⟨x, hx.1, (congrArg (betaM M n j) (hm.2 y)).trans hx.2⟩

private def bl (M : Model l K) (j n : ℕ) : (M.HS true j).lim →ₗ[Acris l] M.MH n j :=
  (B.β (B.schFn M.p) (okToOC l K) true n j).comp ((LinearMap.proj n).comp (M.HS true j).lim.subtype)

private theorem witt_fac (k : Type) [Field k] [CharP k l] [PerfectRing k l] (y : WittVector l k) (hy : y ≠ 0) :
    ∃ (m : ℕ) (b : WittVector l k), y = (l : WittVector l k) ^ m * b ∧ IsUnit b := by
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' y hy
  exact ⟨m, b, e, b.isUnit⟩

private theorem isUnit_l (B₀ : PB l K) : IsUnit (l : B₀.C) := by
  have h : (l : B₀.C) = algebraMap ℚ_[l] B₀.C (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)).map _

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.absInvOf :
    UpperTheory.Ru.crystallineComparison.AbsInvOf := by
  intro l _ K r B₀ hC e he M hM f N j hk hfN hT F hPin hB ϖ hϖ
  obtain ⟨N', rfl⟩ := hfN
  have hg := gRes_pow r f hk
  obtain ⟨⟨Fr, hFr⟩, hρ', -⟩ := frEx l (OK l K) M.X M.p (okToOC l K) (gRes r) (f * N') f hg
  obtain ⟨ρ, hρ⟩ := hρ' (fun x w h => UpperTheory.integersResidue_eq_theta_coeff_pow_of_teichmuller r _ hT x w h)
  refine ⟨f * N', N', gRes r, Fr, ρ, UpperTheory.integersResidue_eq_zero_of_not_isUnit r ϖ hϖ, hg, hFr, hρ, ?_⟩
  intro ι _ v c s hinv
  obtain ⟨⟨u, hsurj, hker⟩, hphi, hgal⟩ := hB
  have hy := UpperTheory.evalEtaleFamily_mem_limit_of_reduced e he.red M j v c
  refine Exists.elim (hsurj ⟨_, hy⟩) fun h hh => ?_
  choose χ hχ using (galA_tA (K := K))
  letI iQ : Module (Acris l) (Pb.AL r M j) := (inferInstance : Module (per l K).A (Pb.AL r M j))
  have hz := chain1 (R := Acris l) (Q := Pb.AL r M j) (H := (M.HS true j).lim) (Γ := K.fixingSubgroup)
    (Mn := fun n => M.MH n j) l (tA l) (phiA l) galA (fun g => zA l (χ g)) (fun n => bl M j n) (fun g => Pb.galL M j g)
    (fun g n => M.galMH (IntermediateField.fixingSubgroupEquiv K g) n j) u s (f * N') (F.α M j) (F.galT M j)
    hker (fun g x n => hgal g x n) (fun n => evE e M j n v c) h hh hχ (phiA_iter_l _) (phiA_iterate_tA _)
    (fun g => phiA_iterate_zA _ _) (F.lin M hM j) (F.gal M hM j)
    (fun g => UpperTheory.galoisAction_evalEtaleFamily_exists_denominator B₀ e he M j s v c g (χ g) (hχ g) hinv)
  have hd := UpperTheory.galois_equivariant_tensor_descent_of_prime_power_units l (W := WittVector l r.k) (A := Pb.AW r) (C := B₀.C) (Γ := K.fixingSubgroup) (L := Pb.LW r M j)
    B₀.c (tA l) galA (fun g => (B₀.σ g).toRingHom) (fun g => zA l (χ g)) (F.galT M j) (F.α M j h) (u + s)
    (witt_fac r.k) (isUnit_l B₀) B₀.t_unit B₀.loc B₀.ker B₀.σ_c hC.1 hχ (fun g a y => F.galT_tmul M hM j g a y) hC.2 hz
  obtain ⟨a', b', y, hab⟩ := hd
  have key := keyStep hk hFr hρ F hPin y
  choose x hx1 hx2 using key
  refine ⟨a' + F.e M j + f * N' * u, b' + u, x, fun n => ⟨hx1 n, ?_⟩⟩
  have hc := chain2 (R := Acris l) (Q := Pb.AL r M j) (H := (M.HS true j).lim) (Mn := fun n => M.MH n j) l (tA l) (phiA l)
    (fun n => bl M j n) (fun x => Pb.phiL M j x) (fun n => phiH M.P n j) u s (f * N') (F.e M j) a' b' (F.α M j) (F.β M j) h
    ((1 : Pb.AW r) ⊗ₜ y) (fun n => evE e M j n v c) (fun n => evE e M j n v fun k => (phiA l)^[f * N'] (c k)) hh
    (phiA_iter_l _) (phiA_iterate_tA _) hab (F.fac M hM j h) (fun x n => hphi x n) (fun n a x => phi_iter_smul M.P n j _ a x)
    (fun n => UpperTheory.crisFrobenius_iterate_evalEtaleFamily e he.phi M j n _ v c) n
  exact hc.trans (congrArg _ (hx2 n))
