import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ClsStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SXiCoh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiTame
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ProdPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LineCoh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeLevelRows.ExistsRowsHeckeCompatibleLevelPrimePow
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeLevelRows.HeckeMatrixMemGammaZeroInfAndExistsUnitInv

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem zmod_val_cast_eq_cast_hom {d M : ℕ} [NeZero M] (h : d ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod d) = ZMod.castHom h (ZMod d) z := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

omit [IsAlgClosure ℚ Ω] in
private theorem xi_scalar_first_entry (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (x y : Row M₀)
    (P : (ZMod M)ˣ → Prop) (c : ZMod M₀) (b : Fam X M₀) :
    Xi X l n N M₀ M w g x y P (fun x y => b (c • x) (c • y)) = Xi X l n N M₀ M w g (c • x) (c • y) P b := by
  funext u
  simp only [Xi, Matrix.smul_vecMul]

private theorem congruence_scalar_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (k k' j : ℕ) (h : (k : ZMod (l ^ n)) = k') (a : X.Fn l) :
    CgF X l n ((k : ℤ_[l]) ^ j • a) ((k' : ℤ_[l]) ^ j • a) := by
  intro u
  refine (sApi Ω ε X l n).2.2.2.2.1 _ _ (a u) (Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ j))
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (k' : ℤ) (k : ℤ) (l ^ n)).1 (by exact_mod_cast h.symm)
  exact ⟨(c : ℤ_[l]), by exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[l]) hc⟩

private theorem xi_hecke_third_relation (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ))
    (hL : Lev l n N M₀ M g) (p : ℕ) (xb yb : Row M₀) (hok : Ok ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb))
    (a : Fam X M₀) (ha : Eqv X (l ^ n) M₀ a) (A : Type) [CommGroup A] (π : (ZMod M)ˣ →* A) (q : (ZMod M)ˣ) (hq : (q : ZMod M) = p)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (ν : (ZMod M)ˣ)
    (h1 : ((ν : ZMod M).val : ZMod N) = (en δ 0 0 : ZMod N)) (h2 : ((ν : ZMod M).val : ZMod (l ^ n)) = 1)
    (h3 : ((ν : ZMod M).val : ZMod N) * (p : ZMod N) = 1) (hπ : π ν = 1) (t : A) :
    CgF X l n ((p : ℤ_[l]) ^ 2 • Xi X l n N M₀ M w g xb yb (fun z => π z = t) a)
      ((p : ℤ_[l]) ^ w • X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ)
        (Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb) (fun z => π z = t * (π q)⁻¹ ^ 2) a)) := by
  have hN : N ∣ M := ⟨M₀, hL.eq⟩
  have hM : M₀ ∣ M := ⟨N, by rw [hL.eq, mul_comm]⟩
  have hln : l ^ n ∣ M := hL.dl.trans hM
  obtain ⟨E, -, hs, -⟩ := sApi Ω ε X l n
  have a1 := sXiAct Ω ε X l n N M₀ M w g hL _ _ hok (fun z => π z = t * (π q)⁻¹ ^ 2) a ha δ hδ ν h1 h2
    (fun z => by simp only [map_mul, map_pow, hπ, one_pow, mul_one])
  have hμ : ((((ν * q : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod N) = 1 := by
    rw [zmod_val_cast_eq_cast_hom hN] at h3 ⊢
    rw [Units.val_mul, hq, map_mul, map_natCast, h3]
  have hμ' : ((((ν * q : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod (l ^ n)) = p := by
    rw [zmod_val_cast_eq_cast_hom hln] at h2 ⊢
    rw [Units.val_mul, hq, map_mul, map_natCast, h2, one_mul]
  have a2 := sXiScal Ω ε X l n N M₀ M w g hL xb yb (fun z => π z = t * (π q)⁻¹ ^ 2) a (ν * q) hμ
  have e1 : ∀ x : Row M₀, (((ν : ZMod M).val : ℕ) : ZMod M₀) • (p : ZMod M₀) • x =
      ((((ν * q : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod M₀) • x := by
    intro x
    rw [smul_smul, zmod_val_cast_eq_cast_hom hM, zmod_val_cast_eq_cast_hom hM, Units.val_mul, hq, map_mul, map_natCast]
  have e2 : (fun z : (ZMod M)ˣ => π (z * (ν * q)⁻¹ ^ 2) = t * (π q)⁻¹ ^ 2) = fun z => π z = t := by
    funext z
    simp only [map_mul, map_pow, map_inv, hπ, one_mul, mul_left_inj]
  rw [e1, e1] at a1
  beta_reduce at a2
  rw [e2] at a2
  exact E.trans (E.symm (congruence_scalar_pow X l n _ p 2 hμ' _)) (E.trans (E.symm a2)
    (E.trans (congruence_scalar_pow X l n _ p w hμ' _) (hs _ _ _ (E.symm a1))))

private theorem xi_hecke_prime_relation (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ))
    (hL : Lev l n N M₀ M g) (hlift : LiftsWith X l N w (cL X l N w)) (p M' : ℕ) [Fact p.Prime] [NeZero M'] [NeZero (p * M₀)]
    (h : M ∣ M') (hM' : M' = N * (p * M₀)) (hp : Nat.Coprime p M) (hpl : Nat.Coprime p l)
    (c d : ℕ) (ws : ∀ (_ M : ℕ), (Ω ≃ₐ[ℚ] Ω) → Fam X M) (hws : Laws X l c d ws) (hLv : Lv c d (p * M₀))
    (xb yb : Row M₀) (hokb : Ok xb yb) (hok : Ok ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb))
    (A : Type) [CommGroup A] (π : (ZMod M)ˣ →* A) (q : (ZMod M)ˣ) (hq : (q : ZMod M) = p)
    (hδ : sgD N l p ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (ν : (ZMod M)ˣ)
    (h1 : ((ν : ZMod M).val : ZMod N) = (en (sgD N l p) 0 0 : ZMod N)) (h2 : ((ν : ZMod M).val : ZMod (l ^ n)) = 1)
    (h3 : ((ν : ZMod M).val : ZMod N) * (p : ZMod N) = 1) (hπ : π ν = 1) :
    CohB X l N w n (fun s => (π (cycM M s))⁻¹)
      (fun s t => (p : ℤ_[l]) • Xi X l n N (p * M₀) M' w g (up p M₀ xb + tp p M₀ ![1, 0]) (up p M₀ yb + tp p M₀ ![0, 1])
        (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws n (p * M₀) s))
      fun s t => (p : ℤ_[l]) • Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb) (fun z => π z = t) (ws n M₀ s) -
        X.heckeT N l p (Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb) (fun z => π z = t * (π q)⁻¹) (ws n M₀ s)) +
        (p : ℤ_[l]) ^ w • X.diam N l p
          (Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb) (fun z => π z = t * (π q)⁻¹ ^ 2) (ws n M₀ s)) := by
  obtain ⟨E, hadd, hs, -⟩ := sApi Ω ε X l n
  obtain ⟨F, fc, fadd, fs, -⟩ := sCohApi Ω ε X l N w n (NeZero.pos N) A (fun s => (π (cycM M s))⁻¹)
  have fs' : ∀ (k : ℤ_[l]) z z', CohB X l N w n (fun s => (π (cycM M s))⁻¹) z z' →
      CohB X l N w n (fun s => (π (cycM M s))⁻¹) (fun s y => k • z s y) fun s y => k • z' s y := by
    intro k z z' hz
    simpa only [mul_one] using fs k 1 z z' hz
  have hpNM : Nat.Coprime p (N * M₀) := hL.eq ▸ hp
  have hLv0 : Lv c d M₀ := ⟨NeZero.pos M₀, hLv.2.1.coprime_mul_left_right, hLv.2.2.coprime_mul_left_right⟩
  have C1 := sXiCoh Ω ε X l n N M₀ M w g hL hlift _ _ hok A π _ _ (hws.dist n p M₀ hLv)
  have C2 := sXiCoh Ω ε X l n N M₀ M w g hL hlift _ _ hokb A π _ _ (hws.lev n p M₀ hLv)
  have C3 := sXiCoh Ω ε X l n N M₀ M w g hL hlift _ _ hokb A π _ _
    (sLineCoh Ω ε X l n N M₀ p c d (by rw [mul_assoc]; exact Nat.Coprime.mul_right hpl hpNM) ws hws hLv)
  have C := (fadd _ _ _ _ (fs' (p : ℤ_[l]) _ _ C1) (fadd _ _ _ _ (fs' ((p : ℤ_[l]) ^ 2) _ _ C2) (fs' (p : ℤ_[l]) _ _ C3)).2).1
  refine F.trans (fc _ _ ?_) (F.trans C (fc _ _ ?_))
  · intro s t
    obtain ⟨m1, m2, -⟩ := sXiMul Ω ε X l n N M₀ M w g hL xb yb hokb (fun z => π z = t)
    have b1 := sXiTame Ω ε X l n N M₀ M w g hL p M' h hM' hp xb yb ![1, 0] ![0, 1] (by simp) (fun z => π z = t) (ws n (p * M₀) s)
    have b2 := m1 (pushB X p M₀ (ws n (p * M₀) s))
      (fun x y => pushD X p M₀ (ws n (p * M₀) s) ((p : ZMod M₀) • x) ((p : ZMod M₀) • y))
      (fun x y => ws n (p * M₀) s (up p M₀ x) (up p M₀ y) ^ p) (pushL X p N M₀ (ws n (p * M₀) s))
      (fun x y _ => ⟨1, by rw [← sPairs Ω ε X p N M₀ hpNM, one_pow, mul_one, mul_div_cancel_right]⟩)
    rw [xi_scalar_first_entry] at b2
    have b3 := m2 (fun x y => ws n (p * M₀) s (up p M₀ x) (up p M₀ y)) p
    have b4 := hs (p : ℤ_[l]) _ _ (E.trans b1 (E.trans b2 (hadd _ _ _ _ (E.refl _) (hadd _ _ _ _ b3 (E.refl _)).2).1))
    simpa only [Pi.add_apply, Pi.sub_apply, smul_add, smul_sub, smul_smul, ← sq] using b4
  · intro s t
    have b1 := sXiHecke Ω ε X l n N M₀ M w g hL p q hq xb yb (fun z => π z = t) (ws n M₀ s)
    have e : (fun z : (ZMod M)ˣ => π (z * q) = t) = fun z => π z = t * (π q)⁻¹ := by
      funext z
      rw [map_mul, eq_mul_inv_iff_mul_eq]
    beta_reduce at b1
    rw [e] at b1
    have b2 := xi_hecke_third_relation X l n N M₀ M w g hL p xb yb hok (ws n M₀ s) ((hws.coc n M₀ hLv0).eqv s) A π q hq _ hδ ν h1 h2 h3 hπ t
    have b3 := (hadd _ _ _ _ (E.refl ((p : ℤ_[l]) • Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb)
      (fun z => π z = t) (ws n M₀ s))) (hadd _ _ _ _ b2 (E.symm b1)).2).1
    rw [sub_add_eq_add_sub, add_sub_assoc]
    exact b3

private theorem sum_filter_fiber_eq {G B : Type} [CommGroup G] [Fintype G] {H ι : Type} [Fintype ι] [AddCommMonoid B] [DecidableEq (G × H)]
    [DecidableEq H] (ρ : ι → G × H) (f : ι → B) (e : G) (y : H) :
    ∑ a : G, ∑ i ∈ Finset.univ.filter (fun i => ρ i = (a * e, y)), f i = ∑ i ∈ Finset.univ.filter (fun i => (ρ i).2 = y), f i := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single ((ρ i).1 * e⁻¹)]
  · simp [Prod.ext_iff]
  · intro a _ ha
    rw [if_neg]
    intro h
    apply ha
    rw [h]
    simp
  · simp

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.kato_norm_relation_tame_prime :
    UpperTheory.V.Z.Kato.Nb.KatoClassHeckeEulerFactorRelation := by
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g H hp hcop ⟨ws, hws⟩ hlift n r
  obtain ⟨F, fc, fadd, fs, -, f0, -, fh⟩ := sCohApi Ω ε X l N w n (NeZero.pos N) (ZMod (l ^ r))ˣ
    (fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact f0 _ _
  haveI : Fact p.Prime := ⟨hp⟩
  have hl : l.Prime := Fact.out
  have hpN : Nat.Coprime p (l * N) := hcop.coprime_mul_right_right.coprime_mul_right_right
  have hpl : Nat.Coprime p l := hpN.coprime_mul_right_right
  have hpN' : Nat.Coprime p N := hpN.coprime_mul_left_right
  haveI : NeZero (N * l ^ (r + n)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (p * (N * l ^ (r + n))) := ⟨mul_ne_zero hp.ne_zero (NeZero.ne _)⟩
  have hL : Lev l n N (N * l ^ (r + n)) (topM l n r (N * N)) g :=
    ⟨by unfold topM; ring, dvd_mul_right _ _, (pow_dvd_pow l (Nat.le_add_left n r)).mul_left _, hn, H.cop, H.g0⟩
  have hL' : Lev l n N (p * (N * l ^ (r + n))) (lvT l n r N p) g :=
    ⟨by unfold lvT; ring, hL.dN.mul_left _, hL.dl.mul_left _, hn, H.cop, H.g0⟩
  have hMM : topM l n r (N * N) ∣ lvT l n r N p := dvd_mul_right _ _
  have hrM : l ^ r ∣ topM l n r (N * N) := (pow_dvd_pow l (Nat.le_add_right r n)).mul_right _
  have hpM : Nat.Coprime p (topM l n r (N * N)) := (hpl.pow_right _).mul_right (hpN'.mul_right hpN')
  have hc : ∀ c : ℕ, Nat.Coprime c (6 * l * N) → Nat.Coprime p c → Nat.Coprime c (p * (N * l ^ (r + n))) := fun c h h' =>
    h'.symm.mul_right (h.coprime_mul_left_right.mul_right (h.coprime_mul_right_right.coprime_mul_left_right.pow_right _))
  have hLv : Lv c d (p * (N * l ^ (r + n))) :=
    ⟨NeZero.pos _, hc c H.cc hcop.coprime_mul_right_right.coprime_mul_left_right, hc d H.cd hcop.coprime_mul_left_right⟩
  have hLv0 : Lv c d (N * l ^ (r + n)) := ⟨NeZero.pos _, hLv.2.1.coprime_mul_left_right, hLv.2.2.coprime_mul_left_right⟩
  obtain ⟨xb, yb, ob, o0, oT, iU, iV, iUT, iVT⟩ := UpperTheory.exists_rows_hecke_compatible_level_prime_pow l N p (r + n) x H.odd H.cop hpN (le_add_left hn)
  obtain ⟨hδ, ν, h1, h2, h3⟩ := UpperTheory.heckeMatrix_mem_gammaZero_inf_and_exists_unit_inv l N p (r + n) H.cop hpN
  let π : (ZMod (topM l n r (N * N)))ˣ →* (ZMod (l ^ r))ˣ := Units.map (ZMod.castHom hrM (ZMod (l ^ r))).toMonoidHom
  let π' : (ZMod (lvT l n r N p))ˣ →* (ZMod (l ^ r))ˣ := Units.map (ZMod.castHom (hrM.trans hMM) (ZMod (l ^ r))).toMonoidHom
  have hππ : ∀ z, π' z = π (Units.map (ZMod.castHom hMM (ZMod (topM l n r (N * N)))).toMonoidHom z) := by
    intro z
    ext
    exact (RingHom.congr_fun (ZMod.castHom_comp hrM hMM) (z : ZMod (lvT l n r N p))).symm
  have hcy := (sSlD Ω ε X N (NeZero.pos N)).2.2.2.2.2.2.2
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have k0 : (fun s : Ω ≃ₐ[ℚ] Ω => (π (cycM (topM l n r (N * N)) s))⁻¹) =
      fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹ := by
    funext s
    rw [(sCycZ Ω l r s).1, ← (hcy (topM l n r (N * N)) s).2.2.2.2 (l ^ r) hrM]
  have kT' : (fun s : Ω ≃ₐ[ℚ] Ω => (π' (cycM (lvT l n r N p) s))⁻¹) =
      fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹ := by
    funext s
    rw [(sCycZ Ω l r s).1, ← (hcy (lvT l n r N p) s).2.2.2.2 (l ^ r) (hrM.trans hMM)]
  have hred : ∀ j, j ≤ r + n → (((ν : ZMod (l ^ (r + n) * (N * N))).val : ℕ) : ZMod (l ^ j)) = 1 := by
    intro j hj
    have := congrArg (ZMod.castHom (pow_dvd_pow l hj) (ZMod (l ^ j))) h2
    rwa [map_natCast, map_one] at this
  have hπ : π ν = 1 := by
    ext
    exact (zmod_val_cast_eq_cast_hom hrM (Units.val ν)).symm.trans (hred r (Nat.le_add_right r n))
  have hq : (π (ZMod.unitOfCoprime p hpM))⁻¹ = inv1 (l ^ r) p := by
    have hu : IsUnit (p : ZMod (l ^ r)) := (ZMod.isUnit_iff_coprime _ _).2 (hpl.pow_right _)
    rw [inv1, dif_pos hu]
    congr 1
    ext
    exact map_natCast (ZMod.castHom hrM (ZMod (l ^ r))) p
  have C := xi_hecke_prime_relation X l n N _ _ w g hL hlift p (lvT l n r N p) hMM hL'.eq hpM hpl c d ws hws hLv xb yb ob o0 _ π
    (ZMod.unitOfCoprime p hpM) rfl hδ ν h1 (hred n (Nat.le_add_left n r)) h3 hπ
  obtain ⟨β, hβ, hβ'⟩ := sTopRel Ω ε X l n N _ _ w g hL hlift c d ws hws hLv0 _ _ o0 _ _ iU iV
  have B0 := sBridge Ω ε X l n N _ _ w g hL hlift _ _ o0 _ (hws.coc n _ hLv0) _ β hβ hβ' _ π
  obtain ⟨βT, hβT, hβT'⟩ := sTopRel Ω ε X l n N _ _ w g hL' hlift c d ws hws hLv _ _ oT _ _ iUT iVT
  have BT := sBridge Ω ε X l n N _ _ w g hL' hlift _ _ oT _ (hws.coc n _ hLv) _ βT hβT hβT' _ π'
  rw [k0] at C B0
  rw [kT'] at BT
  rw [hq] at C
  simp only [← hππ] at C
  have B0' : CohB X l N w n _ (Y0 X l n r N x c d w g) _ := B0
  have D1 := fs (p : ℤ_[l]) 1 _ _ B0'
  have D2 := (fh p hp hpN _ _ (fs 1 (inv1 (l ^ r) p) _ _ B0')).1
  have D3 := fs ((p : ℤ_[l]) ^ w) 1 _ _ (fh p hp hpN _ _ (fs 1 (inv1 (l ^ r) p ^ 2) _ _ B0')).2
  have D4 := fs (p : ℤ_[l]) 1 _ _ BT
  simp only [one_smul, mul_one] at D1 D2 D3 D4
  have D := (fadd _ _ _ _ (fadd _ _ _ _ D1 D2).2 D3).1
  have e : (fun s y => (p : ℤ_[l]) • ∑ a, YT X l n r N p x c d w g s (a, y)) =
      fun s y => (p : ℤ_[l]) • GlobalTheory.KA.push π' (shB X l (lvT l n r N p) (clsT X l n r N p x c d w g)) s y := by
    funext s y
    congr 1
    exact sum_filter_fiber_eq (rdT l n r N p) _ _ y
  rw [e]
  exact F.trans D4 (F.trans C (F.symm D))
