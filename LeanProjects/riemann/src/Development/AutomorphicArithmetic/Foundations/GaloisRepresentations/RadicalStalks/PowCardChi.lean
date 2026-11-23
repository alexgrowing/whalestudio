import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section Helpers

variable {k : Type*} [Field k] {C : Type*} {P : Type*} [AddCommGroup P] [Module k P]

private abbrev Gs (ρ : C → Module.End k P) (ψ : C → k) : Submodule k P :=
  ⨅ c, (ρ c).maxGenEigenspace (ψ c)

private theorem rho_congr [CommRing C] (p : ℕ) [CharP k p] (ρ : C → Module.End k P)
    (add : ∀ x y, ρ (x + y) = ρ x + ρ y) (mul : ∀ x y, ρ (x * y) = ρ x * ρ y) (one : ρ 1 = 1)
    {a b : C} (h : (p : C) ∣ a - b) : ρ a = ρ b := by
  let R : C →+* Module.End k P :=
    { toFun := ρ, map_one' := one, map_mul' := mul, map_add' := add,
      map_zero' := by have := add 0 0; simpa using this }
  have hp : ((p : ℕ) : Module.End k P) = 0 := by
    rw [← map_natCast (algebraMap k (Module.End k P)) p, CharP.cast_eq_zero k p, map_zero]
  obtain ⟨e, he⟩ := h
  have h0 : R (a - b) = 0 := by rw [he, map_mul, map_natCast, hp, zero_mul]
  rw [map_sub] at h0
  exact sub_eq_zero.1 h0

private theorem idem_fix (E : Module.End k P) (h : E * E = E) (v : P)
    (hv : v ∈ E.maxGenEigenspace 1) : E v = v := by
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  rw [one_smul] at hn
  have hNN : (E - 1) * (E - 1) = -(E - 1) := by
    rw [sub_mul, mul_sub, mul_sub, h]; simp
  have key : ∀ n : ℕ, ((E - 1) ^ (n + 1)) v = 0 → (E - 1) v = 0 := by
    intro n
    induction n with
    | zero => intro h0; simpa using h0
    | succ n ih =>
      intro h0
      apply ih
      have h1 : (E - 1) ^ (n + 1 + 1) = -(E - 1) ^ (n + 1) := by
        rw [pow_succ (E - 1) (n + 1), pow_succ (E - 1) n, _root_.mul_assoc, hNN, mul_neg]
      rw [h1] at h0
      simpa using h0
  cases n with
  | zero =>
    have : v = 0 := by simpa using hn
    simp [this]
  | succ n =>
    have := key n hn
    simpa [sub_eq_zero] using this

private theorem Phi_pow {p : ℕ} (Φ : P →+ P) (semi : ∀ (l : k) x, Φ (l • x) = l ^ p • Φ x)
    (T : Module.End k P) (comm : ∀ x, Φ (T x) = T (Φ x)) (s : k) (n : ℕ) (v : P) :
    Φ (((T - s • 1) ^ n) v) = ((T - (s ^ p) • 1) ^ n) (Φ v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    have h1 : Φ ((T - s • 1) v) = (T - (s ^ p) • 1) (Φ v) := by
      simp [comm, semi, map_sub]
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h1]

private theorem Phi_maps {p : ℕ} (Φ : P →+ P) (semi : ∀ (l : k) x, Φ (l • x) = l ^ p • Φ x)
    (ρ : C → Module.End k P) (comm : ∀ c x, Φ (ρ c x) = ρ c (Φ x)) (ψ : C → k) (v : P)
    (hv : v ∈ Gs ρ ψ) : Φ v ∈ Gs ρ (fun c => ψ c ^ p) := by
  refine (Submodule.mem_iInf _).2 fun c => ?_
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hv c)
  exact (Module.End.mem_maxGenEigenspace _ _ _).2
    ⟨n, by rw [← Phi_pow Φ semi (ρ c) (comm c), hn, map_zero]⟩

private theorem proj_gs (ρ : C → Module.End k P) (hI : iSupIndep (Gs ρ)) (hT : ⨆ ψ, Gs ρ ψ = ⊤)
    (T : Module.End k P) (hTm : ∀ ψ, ∀ v ∈ Gs ρ ψ, T v ∈ Gs ρ ψ) (χ : C → k) (u y : P)
    (hy : y ∈ Gs ρ χ) (h : T u = y) : ∃ u₁ ∈ Gs ρ χ, T u₁ = y := by
  classical
  have hu : u ∈ Gs ρ χ ⊔ ⨆ (ψ) (_ : ψ ≠ χ), Gs ρ ψ := by
    rw [← iSup_split_single (Gs ρ) χ, hT]; exact Submodule.mem_top
  obtain ⟨u₁, h₁, u₂, h₂, rfl⟩ := Submodule.mem_sup.1 hu
  have hmap : (⨆ (ψ) (_ : ψ ≠ χ), Gs ρ ψ) ≤ (⨆ (ψ) (_ : ψ ≠ χ), Gs ρ ψ).comap T :=
    iSup₂_le fun ψ hψ v hv =>
      (le_iSup₂_of_le (f := fun (ψ : C → k) (_ : ψ ≠ χ) => Gs ρ ψ) ψ hψ le_rfl : Gs ρ ψ ≤ _) (hTm ψ v hv)
  have h₃ := hmap h₂
  have h₄ : T u₂ ∈ Gs ρ χ := by
    have : T u₂ = y - T u₁ := by rw [← h, map_add]; abel
    rw [this]; exact sub_mem hy (hTm χ _ h₁)
  have h₅ : T u₂ = 0 := (Submodule.disjoint_def.1 (hI χ)) _ h₄ h₃
  exact ⟨u₁, h₁, by rw [← h, map_add, h₅, add_zero]⟩

private theorem semi_surj [IsAlgClosed k] {p : ℕ} (hp : 0 < p) [FiniteDimensional k P] (Φ : P →+ P)
    (semi : ∀ (l : k) x, Φ (l • x) = l ^ p • Φ x) (A B : Submodule k P) (hm : ∀ x ∈ A, Φ x ∈ B)
    (hinj : ∀ x ∈ A, Φ x = 0 → x = 0) (hd : Module.finrank k A = Module.finrank k B) :
    ∀ y ∈ B, ∃ x ∈ A, Φ x = y := by
  classical
  let b := Module.finBasis k A
  have root : ∀ l : k, ∃ m : k, m ^ p = l := fun l => IsAlgClosed.exists_pow_nat_eq l hp
  choose r hr using root
  let v : Fin (Module.finrank k A) → B := fun i => ⟨Φ (b i : P), hm _ (b i).2⟩
  have hsum : ∀ m : Fin (Module.finrank k A) → k,
      Φ (∑ i, m i • (b i : P)) = ∑ i, m i ^ p • Φ (b i : P) := fun m => by
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => semi _ _
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : Φ (∑ i, r (g i) • (b i : P)) = 0 := by
      rw [hsum]
      have := congrArg Subtype.val hg
      simpa [hr, v] using this
    have hmem : (∑ i, r (g i) • (b i : P)) ∈ A :=
      Submodule.sum_mem _ fun i _ => A.smul_mem _ (b i).2
    have h1 := hinj _ hmem h0
    have h2 : ∑ i, r (g i) • b i = 0 := Subtype.ext (by simpa using h1)
    have h3 := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h2 i
    rw [← hr (g i), h3, zero_pow hp.ne']
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [hd])
  intro y hy
  have hy' : (⟨y, hy⟩ : B) ∈ Submodule.span k (Set.range v) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hy'
  refine ⟨∑ i, r (c i) • (b i : P), Submodule.sum_mem _ fun i _ => A.smul_mem _ (b i).2, ?_⟩
  rw [hsum]
  have := congrArg Subtype.val hc
  simpa [hr, v] using this

private theorem pow_card_chi [CommRing C] (χ : C →+* k) {q : ℕ} (hq0 : q ≠ 0)
    (hq : Nat.card (C ⧸ RingHom.ker χ) = q) (c : C) : χ c ^ q = χ c := by
  classical
  haveI : Finite (C ⧸ RingHom.ker χ) := Nat.finite_of_card_ne_zero (by rw [hq]; exact hq0)
  letI := Fintype.ofFinite (C ⧸ RingHom.ker χ)
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  letI : Field (C ⧸ RingHom.ker χ) := Fintype.fieldOfDomain _
  have h := FiniteField.pow_card (Ideal.Quotient.mk (RingHom.ker χ) c)
  rw [← Nat.card_eq_fintype_card, hq] at h
  have h2 := congrArg χ.kerLift h
  rw [map_pow] at h2
  simpa using h2

private theorem pow_ne_chi [CommRing C] {p : ℕ} [Fact p.Prime] (χ : C →+* k) {f j : ℕ}
    (hq : Nat.card (C ⧸ RingHom.ker χ) = p ^ f) (hj : 0 < j) (hjf : j < f) :
    (fun c => χ c ^ p ^ j) ≠ ⇑χ := by
  classical
  intro h
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpj : 1 < p ^ j := Nat.one_lt_pow hj.ne' hp1
  haveI : Finite (C ⧸ RingHom.ker χ) :=
    Nat.finite_of_card_ne_zero (by rw [hq]; exact pow_ne_zero _ (by omega))
  letI := Fintype.ofFinite (C ⧸ RingHom.ker χ)
  let Q : Polynomial k := Polynomial.X ^ p ^ j - Polynomial.X
  have hQ : Q ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hpj
  have hQd : Q.natDegree = p ^ j := FiniteField.X_pow_card_sub_X_natDegree_eq k hpj
  have hsub : Finset.univ.image χ.kerLift ⊆ Q.roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ, Polynomial.IsRoot.def]
    have := congrFun h c
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    simp only [RingHom.kerLift_mk]
    rw [this, sub_self]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (RingHom.kerLift_injective χ), Finset.card_univ,
    ← Nat.card_eq_fintype_card, hq] at h1
  have h2 : p ^ f ≤ p ^ j :=
    h1.trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' Q).trans hQd.le))
  exact absurd h2 (not_le.2 (Nat.pow_lt_pow_right hp1 hjf))

end Helpers

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.alg1 :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ), 0 < f →
      Nat.card (C ⧸ w) = p ^ f → ∀ (π : Par p w f) (χ : C →+* k) (P : Type 1) [AddCommGroup P] [Module k P] (ρ : C → Module.End k P) (F : Submodule k P)
      (Φ : P →+ P), Lin p π χ ρ F Φ →
      ∀ V W : P →+ P, (∀ y, V y = 0 → ∃ z, Φ z = y) → (∀ y, W (Φ^[f - 1] (ρ π.g y)) = V (ρ π.c y)) → (∀ x ∈ F, W (ρ π.ε x) = 0) →
      ∀ x ∈ F, ∃ z, ρ π.ε x = ρ π.g (Φ^[f] z) := by
  intro p _ k _ _ _ C _ w f hf hcard π χ P _ _ ρ F Φ L V W hV hW hWF x hx
  haveI := L.fin
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hcard' : Nat.card (C ⧸ RingHom.ker χ) = p ^ f := by rw [L.ker]; exact hcard
  have hcg := fun {a b : C} => rho_congr p ρ L.add L.mul L.one (a := a) (b := b)
  have hcomm : ∀ a b, Commute (ρ a) (ρ b) := fun a b => by
    show ρ a * ρ b = ρ b * ρ a
    rw [← L.mul, ← L.mul, mul_comm]
  have hmt : ∀ i j (φ : k), Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace φ) ((ρ j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hI : iSupIndep (Gs ρ) := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo ρ hmt
  have hT : ⨆ ψ, Gs ρ ψ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo ρ hmt
      fun _ => Module.End.iSup_maxGenEigenspace_eq_top _
  have hGm : ∀ a ψ, ∀ v ∈ Gs ρ ψ, ρ a v ∈ Gs ρ ψ := fun a ψ v hv =>
    (Submodule.mem_iInf _).2 fun b => hmt a b _ ((Submodule.mem_iInf _).1 hv b)
  have hEE : ρ π.ε * ρ π.ε = ρ π.ε := by
    rw [← L.mul]; exact hcg π.idem
  have hχε : χ π.ε = 1 := by
    have h1 : π.ε - 1 ∈ RingHom.ker χ := by rw [L.ker]; exact π.one
    have h2 : χ (π.ε - 1) = 0 := h1
    rw [map_sub, map_one] at h2
    exact sub_eq_zero.1 h2
  have hχa : χ π.a = 0 := by
    have h1 : π.a ∈ RingHom.ker χ := by rw [L.ker]; exact π.mem
    exact h1
  have hfix : ∀ ψ : C → k, ψ π.ε = 1 → ∀ v ∈ Gs ρ ψ, ρ π.ε v = v := fun ψ h1 v hv =>
    idem_fix _ hEE v (by have := (Submodule.mem_iInf _).1 hv π.ε; rwa [h1] at this)
  have heig : ∀ (ψ : C → k) (v : P), (∀ c, ρ c v = ψ c • v) → v ∈ Gs ρ ψ := fun ψ v h =>
    (Submodule.mem_iInf _).2 fun c => (Module.End.mem_maxGenEigenspace _ _ _).2
      ⟨1, by simp [h c]⟩
  have hstep : ∀ j, ∀ v ∈ Gs ρ (fun c => χ c ^ p ^ j), Φ v ∈ Gs ρ (fun c => χ c ^ p ^ (j + 1)) := by
    intro j v hv
    have h1 := Phi_maps Φ L.semi ρ L.comm _ v hv
    have h2 : (fun c => χ c ^ p ^ (j + 1)) = fun c => (χ c ^ p ^ j) ^ p :=
      funext fun c => by rw [pow_succ, pow_mul]
    rw [h2]; exact h1
  have hinj : ∀ j, 0 < j → j < f → ∀ v ∈ Gs ρ (fun c => χ c ^ p ^ j), Φ v = 0 → v = 0 := by
    intro j hj hjf v hv h0
    have hvF : v ∈ F := (L.kerΦ v).1 h0
    have hE : ρ π.ε v = v := hfix _ (by simp [hχε]) v hv
    have he : ∀ c, ρ c v = χ c • v := fun c => by
      have := L.eig c v hvF
      rwa [hE] at this
    exact Submodule.disjoint_def.1 (hI.pairwiseDisjoint (pow_ne_chi χ hcard' hj hjf)) v hv (heig _ v he)
  have hsurj : ∀ j, 0 < j → j < f → ∀ u ∈ Gs ρ (fun c => χ c ^ p ^ (j + 1)),
      ∃ v ∈ Gs ρ (fun c => χ c ^ p ^ j), Φ v = u := fun j hj hjf =>
    semi_surj hp0 Φ L.semi _ _ (hstep j) (hinj j hj hjf) ((L.dims j).trans (L.dims (j + 1)).symm)
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  have hchain : ∀ n, n ≤ m → ∀ u ∈ Gs ρ (fun c => χ c ^ p ^ (n + 1)),
      ∃ u' ∈ Gs ρ (fun c => χ c ^ p ^ 1), Φ^[n] u' = u := by
    intro n
    induction n with
    | zero => intro _ u hu; exact ⟨u, hu, rfl⟩
    | succ n ih =>
      intro hn u hu
      obtain ⟨v, hv, rfl⟩ := hsurj (n + 1) (by omega) (by omega) u hu
      obtain ⟨u', h1, rfl⟩ := ih (by omega) v hv
      exact ⟨u', h1, by rw [Function.iterate_succ_apply']⟩
  have hit : ∀ (c : C) (n : ℕ) (v : P), Φ^[n] (ρ c v) = ρ c (Φ^[n] v) := by
    intro c n v
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.comm]
  have hye : ∀ c, ρ c (ρ π.ε x) = χ c • ρ π.ε x := fun c => L.eig c x hx
  have hyG : ρ π.ε x ∈ Gs ρ χ := heig _ _ hye
  have hay : ρ π.a (ρ π.ε x) = 0 := by rw [hye, hχa, zero_smul]
  obtain ⟨u, hu⟩ := L.annA _ hay
  have hEy : ρ π.ε (ρ π.ε x) = ρ π.ε x := by
    have := congrArg (fun T : Module.End k P => T x) hEE
    simpa using this
  rw [hEy] at hu
  obtain ⟨u₁, hu₁G, hu₁⟩ := proj_gs ρ hI hT (ρ π.g) (hGm π.g) χ u _ hyG hu.symm
  have hu₁G' : u₁ ∈ Gs ρ (fun c => χ c ^ p ^ (m + 1)) := by
    have h2 : (fun c => χ c ^ p ^ (m + 1)) = ⇑χ := funext fun c => pow_card_chi χ (pow_ne_zero _ hp0.ne') hcard' c
    rw [h2]; exact hu₁G
  obtain ⟨u', hu'G, rfl⟩ := hchain m le_rfl u₁ hu₁G'
  have hEu : ρ π.ε u' = u' := hfix _ (by simp [hχε]) u' hu'G
  have hWy := hWF x hx
  rw [← hu₁, ← hit] at hWy
  have hVz : V (ρ π.c u') = 0 := by
    have := hW u'
    simp only [Nat.add_sub_cancel] at this
    rw [← this]; exact hWy
  obtain ⟨z, hz⟩ := hV _ hVz
  refine ⟨ρ (π.c' * π.ε) z, ?_⟩
  have hΦ : Φ (ρ (π.c' * π.ε) z) = u' := by
    rw [L.comm, hz]
    have h3 : ρ (π.c' * π.ε) * ρ π.c = ρ π.ε := by
      rw [← L.mul]
      apply hcg
      have : π.c' * π.ε * π.c - π.ε = π.c' * π.c * π.ε - π.ε := by ring
      rw [this]; exact π.inv
    have h4 := congrArg (fun T : Module.End k P => T u') h3
    simp only [Module.End.mul_apply] at h4
    rw [h4, hEu]
  rw [Function.iterate_succ_apply, hΦ, hu₁]
