import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtActInternal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TanScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.RigidDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem graded_subalgebra_internal {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    [DecidableEq X] (𝒜 : X → Submodule O R) [SetLike.GradedMonoid 𝒜] (h : iSupIndep 𝒜) :
    DirectSum.IsInternal fun j => (𝒜 j).comap (gradedSub 𝒜).val.toLinearMap := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hs i hi
    have h1 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 h s (fun i => (v i : R)) hv
      (by rw [← AddSubmonoidClass.coe_finset_sum, hs]; rfl) i hi
    exact Subtype.ext h1
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ ⨆ j, 𝒜 j := hx
    induction hx' using Submodule.iSup_induction' with
    | mem i x hi => exact Submodule.mem_iSup_of_mem i hi
    | zero => exact zero_mem _
    | add x y hx1 hy1 ihx ihy => exact add_mem (ihx hx1) (ihy hy1)

private theorem extend_point_degree_zero_graded {O A B K : Type} [CommRing O] [CommRing A] [CommRing B] [CommRing K] [Algebra O A]
    [Algebra O B] [Algebra O K] (𝓑 : ℤ × ℤ → Submodule O B) [GradedAlgebra 𝓑] (φ : A →ₐ[O] B) (X : A →ₐ[O] K)
    (hk : ∀ f, φ f = 0 → X f = 0) (hs : ∀ n, ∀ b ∈ 𝓑 (0, n), ∃ a, φ a = b) (u v : B) (hu : u ∈ 𝓑 (1, 0))
    (hv : v ∈ 𝓑 (-1, 0)) (a₀ : A) (h₀ : φ a₀ = u * v) (c : Kˣ) (hc : X a₀ = c) :
    ∃ Ξ : B →ₐ[O] K, ∀ n a, φ a ∈ 𝓑 (0, n) → Ξ (φ a) = X a := by
  have hk' : ∀ f f', φ f = φ f' → X f = X f' := fun f f' h => by
    rw [← sub_eq_zero, ← map_sub]
    exact hk _ (by rw [map_sub, h, sub_self])
  have hm : ∀ (w : ℤ × ℤ), ∀ f ∈ 𝓑 w, ∀ p q : ℕ, w.1 + p = q → ∃ a, φ a = f * u ^ p * v ^ q := by
    intro w f hf p q h
    have h1 := SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem hf (SetLike.pow_mem_graded p hu))
      (SetLike.pow_mem_graded q hv)
    have h2 : w + p • ((1, 0) : ℤ × ℤ) + q • ((-1, 0) : ℤ × ℤ) = (0, w.2) := by
      ext <;> simp
      omega
    rw [h2] at h1
    exact hs _ _ h1
  have h0 : ∀ w : ℤ × ℤ, w.1 + ((-w.1).toNat : ℕ) = (w.1.toNat : ℕ) := fun w => by omega
  choose g hg using fun (w : ℤ × ℤ) (f : 𝓑 w) => hm w f f.2 _ _ (h0 w)
  let ψ : ∀ w, 𝓑 w →ₗ[O] K := fun w =>
    { toFun := fun f => X (g w f) * ((c⁻¹ : Kˣ) : K) ^ w.1.toNat
      map_add' := fun a b => by
        rw [← add_mul, ← map_add]
        congr 1
        exact hk' _ _ (by rw [map_add, hg, hg, hg, Submodule.coe_add]; ring)
      map_smul' := fun r b => by
        rw [RingHom.id_apply, ← smul_mul_assoc, ← map_smul]
        congr 1
        exact hk' _ _ (by rw [map_smul, hg, hg, Submodule.coe_smul, smul_mul_assoc, smul_mul_assoc]) }
  have hψ : ∀ w (f : 𝓑 w) (p q : ℕ) a, w.1 + p = q → φ a = f * u ^ p * v ^ q → X a = ψ w f * (c : K) ^ q := by
    intro w f p q a h ha
    obtain ⟨d, hd⟩ : ∃ d : ℕ, q = w.1.toNat + d := ⟨q - w.1.toNat, by omega⟩
    have hp : p = (-w.1).toNat + d := by omega
    have e1 : X a = X (g w f * a₀ ^ d) := hk' _ _ (by
      rw [ha, map_mul, map_pow, hg, h₀, hd, hp]; ring)
    show _ = X (g w f) * ((c⁻¹ : Kˣ) : K) ^ w.1.toNat * _
    rw [e1, map_mul, map_pow, hc, hd, pow_add, mul_assoc, ← mul_assoc (_ ^ _), ← mul_pow, Units.inv_mul, one_pow,
      one_mul]
  have hone : ψ 0 (GradedMonoid.GOne.one (A := fun j => 𝓑 j)) = 1 := by
    have := hψ 0 (GradedMonoid.GOne.one (A := fun j => 𝓑 j)) 0 0 1 (by simp) (by simp)
    simpa using this.symm
  have hmul : ∀ {i j} (a : 𝓑 i) (b : 𝓑 j), ψ (i + j) (GradedMonoid.GMul.mul (A := fun j => 𝓑 j) a b) = ψ i a * ψ j b := by
    intro i j a b
    have e1 := hψ i a _ _ _ (h0 i) (hg i a)
    have e2 := hψ j b _ _ _ (h0 j) (hg j b)
    have e3 := hψ (i + j) (GradedMonoid.GMul.mul (A := fun j => 𝓑 j) a b) ((-i.1).toNat + (-j.1).toNat) (i.1.toNat + j.1.toNat)
      (g i a * g j b) (by simp only [Prod.fst_add]; omega)
      (by rw [map_mul, hg, hg, SetLike.coe_gMul]; ring)
    rw [map_mul, e1, e2] at e3
    apply (c.isUnit.pow (i.1.toNat + j.1.toNat)).mul_right_cancel
    rw [← e3]; ring
  refine ⟨(DirectSum.toAlgebra O (fun j => 𝓑 j) ψ hone hmul).comp (DirectSum.decomposeAlgEquiv 𝓑).toAlgHom,
    fun n a ha => ?_⟩
  have h : DirectSum.decompose 𝓑 (φ a) = DirectSum.of (fun j => 𝓑 j) (0, n) ⟨φ a, ha⟩ :=
    DirectSum.decompose_of_mem 𝓑 ha
  have e := hψ (0, n) ⟨φ a, ha⟩ 0 0 a (by simp) (by simp)
  rw [pow_zero, mul_one] at e
  rw [e]
  simp [h, DirectSum.toAlgebra]
  erw [DirectSum.toSemiring_of]
  rfl

private theorem derivation_to_dual_number_point {O A K : Type} [CommRing O] [CommRing A] [Field K] [Algebra O A] [Algebra O K]
    (x : A →ₐ[O] K) (δ : A →ₗ[O] K) (hδ : δ ∈ PtDer x K) :
    ∃ X : A →ₐ[O] DualNumber K, ∀ f, (X f).fst = x f ∧ (X f).snd = δ f := by
  have hδ' : ∀ f g, δ (f * g) = x f • δ g + x g • δ f := hδ
  have h1 : δ 1 = 0 := by
    have := hδ' 1 1
    simpa using this
  refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (δ f)
            map_one' := by ext <;> simp [h1]
            map_mul' := fun f g => by ext <;> simp [hδ', mul_comm]
            map_zero' := by ext <;> simp
            map_add' := fun f g => by ext <;> simp
            commutes' := fun r => by
              rw [Algebra.algebraMap_eq_smul_one (A := A), Algebra.algebraMap_eq_smul_one (A := DualNumber K)]
              ext <;> simp [h1] }, fun f => ?_⟩
  constructor <;> simp

private theorem torus_dual_number_weight_vector (K : Type) [Field K] (a b : K) : ∃ s : (DualNumber K)ˣ × (DualNumber K)ˣ, ∀ w,
    (wv s w : DualNumber K).fst = 1 ∧ (wv s w : DualNumber K).snd = a * w.1 + b * w.2 := by
  let e : Multiplicative K →* DualNumber K :=
    { toFun := fun a => TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr a.toAdd
      map_one' := by ext <;> simp
      map_mul' := fun f g => by ext <;> simp [add_comm] }
  refine ⟨(e.toHomUnits (.ofAdd a), e.toHomUnits (.ofAdd b)), fun w => ?_⟩
  simp only [wv]
  rw [← map_zpow e.toHomUnits, ← map_zpow e.toHomUnits, ← map_mul, MonoidHom.coe_toHomUnits]
  constructor <;> simp [e, mul_comm]

private theorem torus_dual_number_lift_zero (K : Type) [Field K] (t : Kˣ × Kˣ) : ∃ s : (DualNumber K)ˣ × (DualNumber K)ˣ, ∀ w,
    (wv s w : DualNumber K).fst = wv t w ∧ (wv s w : DualNumber K).snd = 0 := by
  let e := Units.map (algebraMap K (DualNumber K) : K →* DualNumber K)
  refine ⟨(e t.1, e t.2), fun w => ?_⟩
  have : wv (e t.1, e t.2) w = e (wv t w) := by simp only [wv, map_mul, map_zpow]
  rw [this]
  constructor <;> simp [e, TrivSqZeroExt.algebraMap_eq_inl]

set_option maxHeartbeats 800000 in
private theorem exists_lift_of_derivation_on_ideal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hL : Loc.LocalPublishedTheorems) (hS : SoV Ω l) (hF : D.Fin0)
    (hN : D.NoEnd) (x : M.A →ₐ[c.O] PadicAlgCl l) (hx : OnS M.eqns.ideal x)
    (h2 : TwoSigned M.gr x) (δ : M.A →ₗ[c.O] PadicAlgCl l) (hδ : δ ∈ PtDer x (PadicAlgCl l))
    (hI : ∀ f ∈ M.eqns.ideal, δ f = 0) : ∃ Ξ : M.SS →ₐ[c.O] DualNumber (PadicAlgCl l),
      ∀ n, ∀ f ∈ M.gr n, (Ξ (M.toSS f)).fst = x f ∧ (Ξ (M.toSS f)).snd = δ f := by
  obtain ⟨hker, hsur, hgr⟩ := kerA D hD M
  obtain ⟨ξ₀, hξ₀⟩ := ptLift D hD M x hx
  have hirr := twoIrr D hD M hL hS hF hN ξ₀ (hξ₀ ▸ h2)
  have hne : ∀ i j, ∃ g, ξ₀ (M.ent g i j) ≠ 0 := fun i j => by
    by_contra hc
    push Not at hc
    have h1 : Submodule.span (PadicAlgCl l) (Set.range (M.rep ξ₀)) ≤
        LinearMap.ker (Matrix.entryLinearMap (PadicAlgCl l) (PadicAlgCl l) i j) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hc g
    rw [hirr] at h1
    simpa using h1 (Submodule.mem_top (x := Matrix.single i j 1))
  obtain ⟨g₁, hg₁⟩ := hne 0 1
  obtain ⟨g₂, hg₂⟩ := hne 1 0
  have hu : (M.ent g₁ 0 1).1 ∈ M.sPart (1, 0) := M.entry_mem g₁ 0 1
  have hv : (M.ent g₂ 1 0).1 ∈ M.sPart (-1, 0) := M.entry_mem g₂ 1 0
  obtain ⟨a₀, -, ha₀⟩ := hsur 0 (M.ent g₁ 0 1 * M.ent g₂ 1 0) (SetLike.GradedMul.mul_mem hu hv)
  have hxa : x a₀ ≠ 0 := by
    rw [← hξ₀, AlgHom.comp_apply, ha₀, map_mul]
    exact mul_ne_zero hg₁ hg₂
  obtain ⟨X, hX⟩ := derivation_to_dual_number_point x δ hδ
  have hXu : IsUnit (X a₀) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [(hX a₀).1]; exact hxa.isUnit)
  let 𝒜 : ℤ × ℤ → Submodule c.O M.SS := fun j => (M.sPart j).comap M.SS.val.toLinearMap
  have hint : DirectSum.IsInternal 𝒜 := graded_subalgebra_internal M.sPart (sInternal D hD M).1
  letI : GradedAlgebra 𝒜 :=
    { toDecomposition := hint.chooseDecomposition
      one_mem := (SetLike.GradedOne.one_mem : (1 : M.S) ∈ M.sPart 0)
      mul_mem := fun _ _ _ _ ha hb => (SetLike.GradedMul.mul_mem ha hb : _ ∈ M.sPart _) }
  obtain ⟨Ξ, hΞ⟩ := extend_point_degree_zero_graded 𝒜 M.toSS X
    (fun f hf => by
      have := (hker f).1 hf
      ext
      · rw [(hX f).1, hx f this]; rfl
      · rw [(hX f).2, hI f this]; rfl)
    (fun n b hb => by obtain ⟨a, -, ha⟩ := hsur n b hb; exact ⟨a, ha⟩) _ _ hu hv a₀ ha₀ hXu.unit rfl
  exact ⟨Ξ, fun n f hf => ⟨(congrArg TrivSqZeroExt.fst (hΞ n f (hgr n f hf))).trans (hX f).1,
    (congrArg TrivSqZeroExt.snd (hΞ n f (hgr n f hf))).trans (hX f).2⟩⟩

set_option maxHeartbeats 800000 in
private theorem derivation_kills_ideal_lifts {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hL : Loc.LocalPublishedTheorems) (hS : SoV Ω l) (hF : D.Fin0)
    (hN : D.NoEnd) (hR : D.AllIrr D.RigidAt) (x : M.A →ₐ[c.O] PadicAlgCl l) (hx : OnS M.eqns.ideal x)
    (h2 : TwoSigned M.gr x) (δ : M.A →ₗ[c.O] PadicAlgCl l) (hδ : δ ∈ PtDer x (PadicAlgCl l))
    (hI : ∀ f ∈ M.eqns.ideal, δ f = 0) : ∃ b : PadicAlgCl l, ∀ n, ∀ f ∈ M.gr n, δ f = b * (n * x f) := by
  obtain ⟨-, -, hgr⟩ := kerA D hD M
  obtain ⟨Ξ, hΞ⟩ := exists_lift_of_derivation_on_ideal D hD M hL hS hF hN x hx h2 δ hδ hI
  let p : DualNumber (PadicAlgCl l) →ₐ[c.O] PadicAlgCl l := TrivSqZeroExt.fstHom c.O _ _
  let q : PadicAlgCl l →ₐ[c.O] DualNumber (PadicAlgCl l) := TrivSqZeroExt.inlAlgHom c.O _ _
  obtain ⟨t, r, hr, hrt⟩ := ptScale D hD M hF (p.comp Ξ)
  obtain ⟨s, hs⟩ := torus_dual_number_lift_zero _ t
  obtain ⟨Ξ₁, -, hΞ₁⟩ := ptAct D hD M (DualNumber (PadicAlgCl l)) Ξ s
  have hfst : ∀ w (f : M.SS), f.1 ∈ M.sPart w → (Ξ₁ f).fst = wv t w * (Ξ f).fst := fun w f hf => by
    rw [hΞ₁ w f hf, TrivSqZeroExt.fst_mul, (hs w).1]
  have hsnd : ∀ w (f : M.SS), f.1 ∈ M.sPart w → (Ξ₁ f).snd = wv t w * (Ξ f).snd := fun w f hf => by
    rw [hΞ₁ w f hf, DualNumber.snd_mul, (hs w).1, (hs w).2, zero_mul, add_zero]
  have hr1 : ∀ g i j, (M.rep Ξ₁ g i j).fst = r g i j := fun g i j => by
    rw [hrt]
    exact hfst _ _ (M.entry_mem g i j)
  have hr2 : M.rep (p.comp Ξ₁) = r := by
    ext g i j
    exact hr1 g i j
  have hpx : ∀ n, ∀ f ∈ M.gr n, (Ξ₁ (M.toSS f)).fst = wv t (0, n) * x f := fun n f hf => by
    rw [hfst _ _ (hgr n f hf), (hΞ n f hf).1]
  have hirr1 : Irr r := by
    rw [← hr2]
    refine twoIrr D hD M hL hS hF hN _ ⟨fun h => h2.1 fun n hn f hf => ?_, fun h => h2.2 fun n hn f hf => ?_⟩
    all_goals
      have h3 : (Ξ₁ (M.toSS f)).fst = 0 := h n hn f hf
      rw [hpx n f hf] at h3
      exact (Units.mul_right_eq_zero _).1 h3
  have hin : D.PtIn _ (M.rep Ξ₁) := tanScale D hD M hF Ξ₁ fun g i j => by
    exact (congrArg (fun z => ‖z - D.r0E g i j‖) (hr1 g i j)).trans_lt ((eptInt D hD r hr).2.1 g i j)
  obtain ⟨a, b, hab⟩ := rigidDiag D hD r hr (hR r hr hirr1) _ hin hr1
  obtain ⟨s', hs'⟩ := torus_dual_number_weight_vector _ a b
  obtain ⟨Ξ₂, -, hΞ₂⟩ := ptAct D hD M (DualNumber (PadicAlgCl l)) (q.comp (p.comp Ξ₁)) s'
  have h2f : ∀ w (f : M.SS), f.1 ∈ M.sPart w → (Ξ₂ f).fst = (Ξ₁ f).fst := fun w f hf => by
    rw [hΞ₂ w f hf, TrivSqZeroExt.fst_mul, (hs' w).1, one_mul]
    rfl
  have h2s : ∀ w (f : M.SS), f.1 ∈ M.sPart w → (Ξ₂ f).snd = (a * w.1 + b * w.2) * (Ξ₁ f).fst := fun w f hf => by
    rw [hΞ₂ w f hf, DualNumber.snd_mul, (hs' w).1, (hs' w).2]
    show 1 * 0 + _ * (Ξ₁ f).fst = _
    rw [mul_zero, zero_add]
  have he : Ξ₂ = Ξ₁ := ptExt D hD M hF (DualNumber (PadicAlgCl l)) _ _ (by
    ext g i j
    · exact h2f _ _ (M.entry_mem g i j)
    · exact ((h2s _ _ (M.entry_mem g i j)).trans (congrArg _ (hr1 g i j))).trans (hab g i j).symm)
  refine ⟨b, fun n f hf => ?_⟩
  have e := h2s _ _ (hgr n f hf)
  subst he
  have e := (hsnd _ _ (hgr n f hf)).symm.trans e
  rw [hpx n f hf, (hΞ n f hf).2] at e
  apply (Units.mul_right_inj (wv t (0, n))).1
  rw [e]
  simp only [Int.cast_zero]
  ring

theorem UpperTheory.V.GradeZeroInterpolatingElement.m4 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], Loc.LocalPublishedTheorems → SoV Ω l → D.Fin0 → D.NoEnd → D.AllIrr D.RigidAt → Alg.M4 M.gr (PadicAlgCl l) M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hL hS hF hN hR x hx h2 δ hδ δ' hδ' hI hI'
  obtain ⟨b, hb⟩ := derivation_kills_ideal_lifts D hD M hL hS hF hN hR x hx h2 δ hδ hI
  obtain ⟨b', hb'⟩ := derivation_kills_ideal_lifts D hD M hL hS hF hN hR x hx h2 δ' hδ' hI'
  have key : ∀ c₁ c₂ : PadicAlgCl l, c₁ * b + c₂ * b' = 0 → c₁ • δ + c₂ • δ' = 0 := fun c₁ c₂ h => by
    ext f
    induction f using DirectSum.Decomposition.inductionOn M.gr with
    | zero => exact map_zero _
    | @homogeneous n f =>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hb n f f.2, hb' n f f.2,
        LinearMap.zero_apply]
      linear_combination ((n : PadicAlgCl l) * x f) * h
    | add f g hf hg => rw [map_add, hf, hg]; simp
  by_cases h0 : b = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, key _ _ (by simp [h0])⟩
  · exact ⟨b', -b, Or.inr (neg_ne_zero.2 h0), key _ _ (by ring)⟩
