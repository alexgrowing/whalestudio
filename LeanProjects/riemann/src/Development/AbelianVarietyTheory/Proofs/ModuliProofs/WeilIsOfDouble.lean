import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsConstOfCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.WeilIsExpRiemannForm

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodPoint

open CechPic

theorem exists_form {M V : Type} [AddCommGroup M] [AddCommGroup V] (P : M →+ V) (hP : Function.Injective P)
    (B : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) (Λ : Submodule ℤ V) (hΛ : ∀ z, z ∈ Λ ↔ z ∈ P.range) :
    ∃ Ef : LinearMap.BilinForm ℤ Λ, Function.Bijective Ef ∧
      ∀ a b (ha : P a ∈ Λ) (hb : P b ∈ Λ), Ef ⟨P a, ha⟩ ⟨P b, hb⟩ = B a b := by
  let φ : M ≃ₗ[ℤ] Λ := LinearEquiv.ofBijective
    (P.toIntLinearMap.codRestrict Λ fun a => (hΛ _).2 ⟨a, rfl⟩)
    ⟨fun a b h => hP (congrArg Subtype.val h), fun z => by
      obtain ⟨a, ha⟩ := (hΛ z).1 z.2
      exact ⟨a, Subtype.ext ha⟩⟩
  refine ⟨LinearMap.BilinForm.congr φ B, ?_, fun a b ha hb => ?_⟩
  · have : ⇑(LinearMap.BilinForm.congr φ B) = φ.symm.dualMap ∘ B ∘ φ.symm := by
      funext x; ext y; simp
    rw [this]
    exact φ.symm.dualMap.bijective.comp (hB.comp φ.symm.bijective)
  · have e : ∀ a (ha : P a ∈ Λ), φ.symm ⟨P a, ha⟩ = a := fun a _ => φ.symm_apply_apply a
    rw [LinearMap.BilinForm.congr_apply, e, e]

theorem weilIs_of_isAH (laws : Out.Laws) (Q : Out.PolAV (Sp ℂ)) {g : ℕ} (hg : Q.g = g) (u : HolUnif Q.A Q.L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (Ef : LinearMap.BilinForm ℤ u.Λ)
    (hE : ∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (k : ℕ) (a b : u.Λ) (c : ℂˣ) (hk : 0 < k)
    (hc : (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k)) :
    Out.WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin g → ℂ))) (unitOn c) := by
  subst hg
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  exact WeilExp.weilIs_exp_riemannForm laws.weil hval (@eq_of_valAt'_eq hval hvalaff) @isReduced_of_smooth_complex
    (ThetaGroupFrame.thetaGrp_in_frame hval (@holFamily_lift hval)) Q u Hm χ Ef ⟨h.1, h.2.2.1, hE, h.2.2.2⟩ k a b c hk hc

theorem cls_of_lam_eq {S : Scheme.{0}} [IsLocallyNoetherian S] (laws : Out.Laws) (Q : Out.PolAV S) [IsCommMonObj Q.A]
    (hΘ : ∃ t : LB.Gen (Theta Q.A Q.L), t.IsGen) (PP : RigLB Q.A) (hs : PP.IsSymmetric)
    (h : LBIso (abelian₂ Q.A PP.L) (abelian₂ Q.A Q.L)) :
    2 • cls PP.L PP.isLB = 2 • cls Q.L Q.isLB ∧
      pull ((𝟙 Q.A : Q.A ⟶ Q.A) ^ 2).left (cls PP.L PP.isLB) = 4 • cls Q.L Q.isLB := by
  set l := cls Q.L Q.isLB with hl
  set p := cls PP.L PP.isLB with hp
  have hlam : ∀ x y : Q.A ⟶ Q.A, lam p x y = lam l x y := fun x y => by
    have h₁ := (cls_eq_iff (LB.isLB_linComb PP.isLB _ _) (LB.isLB_linComb Q.isLB _ _)).2 h
    have h₂ := congrArg (pull (lift x y).left)
      ((cls_cube_two PP.isLB _ _ _).symm.trans (h₁.trans (cls_cube_two Q.isLB _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd] using h₂
  have hz : ∀ (M : LB Q.A.left) (hM : M.IsLB), Out.Rigidified Q.A M → pull (1 : Q.A ⟶ Q.A).left (cls M hM) = 0 := by
    intro M hM hr
    have h₀ := (cls_eq_zero_iff (pull_isLB hM (eSec Q.A))).2 hr
    rw [cls_pull hM] at h₀
    rw [Hom.one_def, Over.comp_left, pull_comp]
    exact (congrArg _ h₀).trans (map_zero _)
  have hl0 : pull (1 : Q.A ⟶ Q.A).left l = 0 := hz Q.L Q.isLB Q.rigid
  have hp0 : pull (1 : Q.A ⟶ Q.A).left p = 0 := hz PP.L PP.isLB ⟨PP.rig, PP.rigGen⟩
  have hl2 : pull ((𝟙 Q.A : Q.A ⟶ Q.A) * 𝟙 Q.A).left l = 4 • l := by
    have h₀ := (cls_eq_zero_iff (LB.isLB_linComb Q.isLB _ _)).2 (laws.mulPull S Q 2)
    rw [cls_linComb Q.isLB, Fin.sum_univ_two] at h₀
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id] at h₀
    have e : Out.mulA Q.A 2 = 𝟙 Q.A * 𝟙 Q.A := by rw [← pow_two]
    rw [e, ← hl] at h₀
    norm_num at h₀
    rw [add_neg_eq_zero] at h₀
    rw [← h₀]; rfl
  have hpi : pull ((𝟙 Q.A : Q.A ⟶ Q.A)⁻¹).left p = p := by
    obtain ⟨_, w, hw, -⟩ := hs
    have e := (cls_eq_iff PP.isLB (pull_isLB PP.isLB _)).2 ⟨w, hw⟩
    rw [cls_pull PP.isLB] at e
    rw [Hom.inv_def, Category.id_comp]
    exact e.symm
  have e₁ : lam l (𝟙 Q.A) (𝟙 Q.A) = 2 • l := by
    simp only [lam, hl2, Over.id_left, pull_id, hl0]; abel
  have e₂ : lam l (𝟙 Q.A)⁻¹ (𝟙 Q.A) = -(2 • l) := by
    have := lam_mul_left Q.isLB hΘ (𝟙 Q.A) (𝟙 Q.A)⁻¹ (𝟙 Q.A)
    rw [mul_inv_cancel, lam_one_left, ← hl, e₁] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have e₃ : lam p (𝟙 Q.A)⁻¹ (𝟙 Q.A) = -(2 • p) := by
    simp only [lam, inv_mul_cancel, hpi, Over.id_left, pull_id, hp0]; abel
  have e₄ : 2 • p = 2 • l := neg_injective (e₃.symm.trans ((hlam _ _).trans e₂))
  refine ⟨e₄, ?_⟩
  have e₅ := (hlam (𝟙 Q.A) (𝟙 Q.A)).trans e₁
  simp only [lam, Over.id_left, pull_id, hp0] at e₅
  rw [pow_two]
  calc _ = (pull ((𝟙 Q.A : Q.A ⟶ Q.A) * 𝟙 Q.A).left p - p - p + 0) + 2 • p := by abel
    _ = 4 • l := by rw [e₅, e₄]; abel

theorem weilIs_of_double (laws : Out.Laws) (Q Q' : Out.PolAV (Sp ℂ)) [IsCommMonObj Q.A] (ψ : Q.A ⟶ Q'.A) [IsMonHom ψ]
    (h : LBIso (lbPow Q.L 4) (Q'.L.pull ψ.left)) (k : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A) (c : Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ)
    (hx : (x ≫ ψ) ^ k = 1) (hy : (y ≫ ψ) ^ k = 1) (hc : Out.WeilIs Q.A Q.L ((k * 4 : ℕ) : ℤ) x y c) :
    Out.WeilIs Q'.A Q'.L k (x ≫ ψ) (y ≫ ψ) c := by
  obtain ⟨c', hc', -⟩ := (laws.weil _ Q' k _).1 _ _ hx hy
  have h₁ := (weilIs_along_hom laws.globalFns _ Q.A Q'.A ψ Q.L Q'.L 4 k _ x y c' c' Q.isAb Q'.isAb Q.isLB Q'.isLB
    inferInstance h hc').1
  rw [Nat.cast_mul] at hc
  rwa [CommutatorPairing.weilIs_unique laws.globalFns Q.isAb Q.isLB hc h₁]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_act (hom : (∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f)) (Q : Out.PolAV (Sp ℂ)) {g : ℕ} (hg : Q.g = g) (u : HolUnif Q.A Q.L g)
    (ty : Fin g → (E →+* ℂ)) (hΛ : ∀ (a : 𝓞 E), ∀ z ∈ u.Λ, (fun k => ty k (a : E) * z k) ∈ u.Λ) :
    ∃ act : OAct (𝓞 E) Q.A, ∀ (a : 𝓞 E) z, u.ex (fun k => ty k (a : E) * z k) = u.ex z ≫ act.act a := by
  have h : ∀ a : 𝓞 E, ∃ f : Q.A ⟶ Q.A, IsMonHom f ∧ ∀ z, u.ex (fun k => ty k (a : E) * z k) = u.ex z ≫ f := fun a =>
    hom Q Q g u u (LinearMap.pi fun k => ty k (a : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) k) hg hg fun z hz => hΛ a z hz
  choose f hf hex using h
  have := Q.isAb.smooth
  have := Q.isAb.proper
  have : IsReduced Q.A.left := isReduced_of_smooth_complex _ Q.A.hom inferInstance
  have ext : ∀ f f' : Q.A ⟶ Q.A, (∀ z, u.ex z ≫ f = u.ex z ≫ f') → f = f' := fun f f' h =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u.ex_onto x
      exact h z
  refine ⟨⟨f, hf, ext _ _ fun z => ?_, fun a b => ext _ _ fun z => ?_, fun a b => ext _ _ fun z => ?_⟩, hex⟩
  · rw [← hex, Category.comp_id]; simp
  · rw [← Category.assoc, ← hex, ← hex, ← hex]
    congr 1; funext k; push_cast; rw [map_mul]; ring
  · rw [MonObj.comp_mul, ← hex, ← hex, ← hex, ← u.ex_add]
    congr 1; funext k; push_cast; rw [map_add, Pi.add_apply]; ring

theorem ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ) (z : Fin g → ℂ) :
    u.ex z ^ n = u.ex (n • z) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, (u.ker 0).2 (zero_mem _)]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, u.ex_add]

theorem exists_triple (laws : Out.Laws) (cube : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)) (tor : (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (χ : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v))) (hom : (∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f))
    (adjW : (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L))) (prim : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (act : OAct (𝓞 E) B) (M : LB B.left), IsAbelianScheme B → M.IsLB → (∃ t : LB.Gen (Theta B M), t.IsGen) → (∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)) → ∃ (PP : RigLB B) (_ : CubicalStr B PP), PP.IsSymmetric ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0] M) ∧ LBIso (abelian₂ B PP.L) (abelian₂ B M) ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0] PP.L) ∧ ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] PP.L) (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] PP.L))) (princ : (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (n : ℕ) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g → LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂ P.A (M.pull ψ.left)) → Out.KTriv B M)) (amp : (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (M : LB B.left) (n : ℕ), 0 < n → IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsFinite ψ.left → (Out.RelAmple B M → Out.RelAmple A (M.pull ψ.left)) ∧ (Out.RelAmple B (lbPow M n) ↔ Out.RelAmple B M) ∧ (Flat ψ.left → Surjective ψ.left → Out.RelAmple A (M.pull ψ.left) → Out.RelAmple B M) ∧ ∀ M' : LB B.left, M'.IsLB → LBIso M M' → Out.RelAmple B M → Out.RelAmple B M'))
    {H : Host E} (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) :
    ∃ (t : SAB H (Sp ℂ)) (L : LB t.G.left) (u : HolUnif t.G L g), IsAbelianScheme t.G ∧
      SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧
      (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
      (∀ z, u.ex z = 1 ↔ z ∈ P.range) ∧
      (∀ (a : 𝓞 E) z, u.ex (fun k => ty k (a : E) * z k) = u.ex z ≫ t.act.act a) ∧
      ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
        Out.WeilIs t.G t.PP.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hE : ∀ (Λ : Submodule ℤ (Fin g → ℂ)), (∀ z, z ∈ Λ ↔ z ∈ P.range) → ∃ Ef : LinearMap.BilinForm ℤ Λ,
      Function.Bijective Ef ∧ (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
      ∀ a b (ha : P a ∈ Λ) (hb : P b ∈ Λ), Ef ⟨P a, ha⟩ ⟨P b, hb⟩ = D.EF a b := fun Λ hΛ => by
    obtain ⟨Ef, h₁, h₂⟩ := exists_form P hinj D.EF D.unimod Λ hΛ
    refine ⟨Ef, h₁, ?_, h₂⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := (hΛ a).1 ha
    obtain ⟨b, rfl⟩ := (hΛ b).1 hb
    rw [h₂, him]
  obtain ⟨Ef₀, hb₀, hi₀, -⟩ := hE P.range.toIntSubmodule fun _ => Iff.rfl
  obtain ⟨Q, u, χ, hg, hΛ, hAH, ht₁, ht₂⟩ := tor g P.range.toIntSubmodule Hm Ef₀ hdisc hspan hH hpos hi₀ hb₀
  have hmem : ∀ z, z ∈ u.Λ ↔ z ∈ P.range := fun z => by rw [hΛ]; rfl
  obtain ⟨Ef, -, hi, hEf⟩ := hE u.Λ hmem
  have hker : ∀ z, u.ex z = 1 ↔ z ∈ P.range := fun z => (u.ker z).trans (hmem z)
  have hW : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c) := fun k a b c hk hc =>
    weilIs_of_isAH laws Q hg u hAH Ef hi k ⟨P a, (hmem _).2 ⟨a, rfl⟩⟩ ⟨P b, (hmem _).2 ⟨b, rfl⟩⟩ c hk (by rwa [hEf])
  obtain ⟨act, hact⟩ := exists_act hom Q hg u ty fun a z hz => by
    obtain ⟨x, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨a • x, funext (hlin a x)⟩
  have hact' : ∀ (a : 𝓞 E) (s : ℂ) x, u.ex (s • P x) ≫ act.act a = u.ex (s • P (a • x)) := fun a s x => by
    rw [← hact]; congr 1; funext k
    simp only [Pi.smul_apply, hlin, smul_eq_mul]; ring
  have htors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A), 0 < n → x ^ n = 1 → ∃ a, x = u.ex ((n : ℂ)⁻¹ • P a) := by
    intro n x hn hx
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [ex_pow, hker] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  have hA := Q.isAb
  have := hA.comm
  have adj : ∀ a, LBIso (cubeLB Q.A ![fst Q.A Q.A ≫ act.act a, snd Q.A Q.A] Q.L)
      (cubeLB Q.A ![fst Q.A Q.A, snd Q.A Q.A ≫ act.act (H.bar a)] Q.L) := fun a => by
    refine adjW ℂ Q _ _ (act.hom a) (act.hom _) fun n x y c hn hx hy hc => ?_
    obtain ⟨x, rfl⟩ := htors n x hn hx
    obtain ⟨y, rfl⟩ := htors n y hn hy
    rw [hact'] at hc ⊢
    let c₀ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (D.EF (a • x) y : ℂ) / n))
    rw [CommutatorPairing.weilIs_unique laws.globalFns hA Q.isLB hc (hW n _ _ c₀ hn rfl)]
    exact hW n _ _ c₀ hn (by rw [← D.adj]; rfl)
  have hΘ := cube _ Q Q.L Q.isLB
  obtain ⟨PP, cub, hsym, -, hlam, hprim, hadj⟩ := prim E H _ Q.A act Q.L hA Q.isLB hΘ adj
  obtain ⟨h₂, h₄⟩ := cls_of_lam_eq laws Q hΘ PP hsym hlam
  have hL := Q.isLB
  have hP' := PP.isLB
  have hid : IsFinite (𝟙 Q.A : Q.A ⟶ Q.A).left := by rw [Over.id_left]; infer_instance
  have hpow : ∀ (M : LB Q.A.left), M.IsLB → ∀ n, (lbPow M n).IsLB := fun M hM n => LB.isLB_linComb hM _ _
  have a₁ : Out.RelAmple Q.A (lbPow Q.L 2) := (amp _ Q.A Q.A (𝟙 _) Q.L 2 two_pos hA hA hL hid).2.1.2 Q.ample
  have a₂ : Out.RelAmple Q.A (lbPow PP.L 2) :=
    (amp _ Q.A Q.A (𝟙 _) _ 1 one_pos hA hA (hpow _ hL 2) hid).2.2.2 _ (hpow _ hP' 2)
      (by rw [← cls_eq_iff (hpow _ hL 2) (hpow _ hP' 2), cls_lbPow hL, cls_lbPow hP', h₂]) a₁
  have a₃ : Out.RelAmple Q.A PP.L := (amp _ Q.A Q.A (𝟙 _) PP.L 2 two_pos hA hA hP' hid).2.1.1 a₂
  have a₄ : Out.KTriv Q.A PP.L := by
    refine princ ℂ Q 1 Q.A (𝟙 _) PP.L one_pos hA hP' inferInstance hid (by rw [Over.id_left]; infer_instance)
      (by rw [Over.id_left]; infer_instance) (by simp) ?_
    refine (cls_eq_iff (LB.isLB_linComb (hpow _ hL 1) _ _) (LB.isLB_linComb (pull_isLB hP' _) _ _)).1 ?_
    refine (cls_cube_two (hpow _ hL 1) _ _ _).trans (Eq.trans ?_ (cls_cube_two (pull_isLB hP' _) _ _ _).symm)
    rw [cls_lbPow hL, cls_pull hP', Over.id_left, pull_id, one_nsmul]
    have h₁ := (cls_eq_iff (LB.isLB_linComb hP' _ _) (LB.isLB_linComb hL _ _)).2 hlam
    exact ((cls_cube_two hP' _ _ _).symm.trans (h₁.trans (cls_cube_two hL _ _ _))).symm
  let Q' : Out.PolAV (Sp ℂ) :=
    { A := Q.A, isAb := hA, g := Q.g, smoothDim := Q.smoothDim, L := PP.L, isLB := hP',
      rigid := ⟨PP.rig, PP.rigGen⟩, sym := sym_of_isSymmetric PP hsym, ample := a₃, ktriv := a₄ }
  refine ⟨{ G := Q.A, semi := isSemiAbelian_of_isAbelianScheme Q.A hA, act := act, PP := PP, cub := cub, sym := hsym,
            adj := hadj, prim := hprim }, Q.L, u, hA, hg ▸ Q.smoothDim, a₃, a₄, ht₁, ht₂, hker, hact,
    fun k a b c hk hc => ?_⟩
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hdbl : IsMonHom ((𝟙 Q.A : Q.A ⟶ Q.A) ^ 2) := laws.rigidity _ _ _ hA hA _ (by
    have e₁ : (η[Q.A] : 𝟙_ _ ⟶ Q.A) = 1 := by rw [Hom.one_def]; simp
    rw [MonObj.comp_pow, Category.comp_id, e₁, one_pow])
  have hx : ∀ a, u.ex (((k * 4 : ℕ) : ℂ)⁻¹ • P (2 • a)) ≫ (𝟙 Q.A : Q.A ⟶ Q.A) ^ 2 = u.ex ((k : ℂ)⁻¹ • P a) := fun a => by
    rw [MonObj.comp_pow, Category.comp_id, ex_pow, map_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    clear * - hk'
    push_cast; field_simp; norm_num
  have hx' : ∀ a, u.ex ((k : ℂ)⁻¹ • P a) ^ k = 1 := fun a => by
    rw [ex_pow, hker, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk']
    exact ⟨a, rfl⟩
  have := weilIs_of_double laws Q Q' ((𝟙 Q.A : Q.A ⟶ Q.A) ^ 2)
    (by rw [← cls_eq_iff (hpow _ hL 4) (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', h₄]) k _ _ (unitOn c)
    ((congrArg (· ^ k) (hx a)).trans (hx' a)) ((congrArg (· ^ k) (hx b)).trans (hx' b))
    (hW (k * 4) (2 • a) (2 • b) c (by positivity) (by
      rw [hc]; congr 1
      rw [map_nsmul, map_nsmul, LinearMap.smul_apply]
      clear * - hk'
      simp only [nsmul_eq_mul]
      push_cast; field_simp; ring))
  rw [hx, hx] at this
  exact this

end GlobalTheory.PeriodPoint
