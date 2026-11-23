import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfCoprime

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSSymm

theorem exists_leftInverse {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {g : ℕ}
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [hf : IsMonHom f] {m : ℕ} (hm : 0 < m)
    (hker : ∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ f = 1 → x ^ m = 1) :
    ∃ h : B ⟶ A, IsMonHom h ∧ f ≫ h = 𝟙 A ^ m := by
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have := hA.comm
  have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite f.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B f hf inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hm
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ m = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ m = 1} => z.1) e)
  have hflat : Flat f.left :=
    SemiAbMulFlat.flat_of_flatOver_fields f.left B.hom inferInstance
      (by rw [Over.w]; infer_instance) (by rw [Over.w]; infer_instance) inferInstance
      fun k _ s => FibreFlat.flatOver_of_pullback f s (IsogenyQuasiInverse.flat_fibre A B g hA hB hAg hBg f k s)
  have hsurj : Surjective f.left :=
    AbLaw.MulN.surjective_of_geomFibres f fun K _ _ t =>
      (IsogenyQuasiInverse.flat_surjective_geomFibre A B g hA hB hAg hBg f K t).2
  have hmA : IsMonHom (𝟙 A ^ m) := AbLaw.MulN.isMonHom_mulA A m
  exact (exists_monHom_factor_of_flat_surjective _ A B A f (𝟙 A ^ m) hf hmA
    hflat hsurj inferInstance fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hker T x hx]).1

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R))

theorem additive [IsTotallyReal F] (c : 𝔠.elt) : IsAdditive (X.P c) ∧ IsAdditive (swap (X.P c)) := by
  obtain ⟨c₁, hc₁⟩ := fracId_exists_totPos F 𝔠
  have hL := pull_isLB (X.isLB c₁) (lift (𝟙 X.A) (𝟙 X.A)).left
  obtain ⟨H, hH, hamp⟩ := BirigidLift.exists_relAmple_prod X.ab X.ab hL (X.pos c₁ hc₁) hL (X.pos c₁ hc₁)
  exact BirigidLift.additive_of_triv X.ab X.ab hH hamp (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem cupSquare (HR : AbelianDeRham) : CupSquare (dp0 R) (𝟙 _) (X.A ⊗ X.A) :=
  cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)

variable {X}

theorem nsmul_eq_zero_of_radical [IsTotallyReal F] (HR : AbelianDeRham) (HD : DualAbelianScheme) {c : 𝔠.elt} {m : ℕ}
    (hm0 : 0 < m) (hm : ∀ d : 𝔠.elt, ∃ t : 𝓞 F, (m : 𝓞 F) • d = t • c) {ψ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hψ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) ψ) {y : HdR X.A} (hy : ∀ x, ψ x y = 0) : m • y = 0 := by
  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD (Sp R) X.A X.ab
  have hBg := hBg _ X.dim
  obtain ⟨a₁, a₂⟩ := additive X c
  obtain ⟨lam, hlam, hcls⟩ := BirigidLift.exists_hom hd hd'.additive (X.isLB c) a₁ a₂
  have hker : ∀ (T : Over (Sp R)) (x : T ⟶ X.A), x ≫ lam = 1 → x ^ m = 1 := by
    intro T x hx
    have tr : Triv (ev (X.P c) (fst X.A T) (snd X.A T ≫ x)) := by
      rw [triv_ev_iff (X.isLB c), BirigidLift.evc_of_cls hd.isLB (X.isLB c) hcls, Category.assoc, hx, comp_one]
      exact evc_one_right hd.isLB hd.zero _
    have k := X.ker c T x tr (m : 𝓞 F) hm
    rwa [PolPrimeTo.act_natCast, comp_pow, Category.comp_id] at k
  obtain ⟨μ', hμ', e₁⟩ := exists_leftInverse X.ab hB X.dim hBg lam hm0 hker
  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := AbelianDualCrystal.duality HR X.ab X.dim hB hBg (hd.isPerfect hd')
  have e : LBIso (ev Q (fst X.A X.A) (snd X.A X.A ≫ lam)) (ev (X.P c) (fst X.A X.A ≫ 𝟙 X.A) (snd X.A X.A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB (X.isLB c) _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev (X.isLB c), BirigidLift.evc_of_cls hd.isLB (X.isLB c) hcls, Category.comp_id]
  have z : push (dp0 R) (𝟙 _) lam y = 0 := (injective_iff_map_eq_zero _).1 (hperf φ hφ).1.bijective_right.1 _ <|
    LinearMap.ext fun x ↦ by
      have k := IsCorrForm.adjoint (cupSquare X HR) hd.isLB (X.isLB c) hφ hψ (𝟙 X.A) lam e x y
      rw [push_id] at k
      exact k.trans (hy _)
  haveI := PolPrimeTo.isMonHom_id_pow X.A m
  have k := push_push (κ := dp0 R) (t := 𝟙 _) lam μ' _ e₁ y
  rw [z, map_zero, PolPrimeTo.push_id_pow] at k
  rw [← Nat.cast_smul_eq_nsmul R]
  exact k.symm

theorem form_smul (HR : AbelianDeRham) {c d : 𝔠.elt} {b : 𝓞 F} (e : d = b • c)
    {φ χ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ)
    (hχ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P d) χ) (x y : HdR X.A) :
    χ x y = φ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  subst e
  have := X.rm.hom
  obtain ⟨χ', hχ', k⟩ := hφ.pull (X.isLB c) (homMor (dp0 R) (𝟙 _) (𝟙 X.A))
    (homMor (dp0 R) (𝟙 _) (X.rm.act b)) (h := (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)).left)
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (X.isLB (b • c)) (LBIso.symm (X.smul b c))
  obtain rfl := hχ.unique (cupSquare X HR) (X.isLB (b • c)) hχ'
  have e := k (push (dp0 R) (𝟙 _) (𝟙 X.A) x) x (push (dp0 R) (𝟙 _) (X.rm.act b) y) y (fun _ ↦ rfl) fun _ ↦ rfl
  rwa [push_id, LinearMap.id_apply, RingHom.id_apply] at e

variable (X) in

theorem exists_form_of (HR : AbelianDeRham) (c : 𝔠.elt) : ∃ φ, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ :=
  exists_isCorrForm (cupSquare X HR) (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem form_skew (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) (x y : HdR X.A) : φ x y = -φ y x :=
  JetIsotropic.corrForm_antisymm (cupSquare X HR) (X.isLB c) (X.symm c) hφ x y

theorem form_balanced (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) (s : R ⊗[ℤ] 𝓞 F) (x y : HdR X.A) :
    φ (actAlg (dp0 R) (𝟙 _) X.rm s x) y = φ x (actAlg (dp0 R) (𝟙 _) X.rm s y) := by
  induction s with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul r b =>
    obtain ⟨χ, hχ⟩ := exists_form_of X HR (b • c)
    rw [actAlg_tmul, actAlg_tmul, map_smul, map_smul, LinearMap.smul_apply, form_skew HR hφ,
      ← form_smul HR rfl hφ hχ, ← form_smul HR rfl hφ hχ, form_skew HR hχ x]

theorem form_fil (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) : ∀ a ∈ Fil X.A, ∀ b ∈ Fil X.A, φ a b = 0 := by
  intro a ha b hb
  obtain ⟨ψ, hψ, eψ⟩ := hφ.isPolForm
  have t := (HR.2.2.2.2 R _ _ (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim) _
    (X.isLB c) ψ hψ).1 _ (push_mem_Fil (inl X.A X.A) ha) _ (push_mem_Fil (inr X.A X.A) hb)
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_one] at t
  simpa using t

theorem form_symm [IsTotallyReal F] (HR : AbelianDeRham) (HD : DualAbelianScheme) (hX : X.IsRapoport)
    (hL : LieExact X.A) {κ : Fil X.A →ₗ[R] X.Lie} (hκ : X.IsLinearKS κ) {c : 𝔠.elt}
    {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) {f f' : Fil X.A}
    {k k' : HdR X.A} (hk : hL.toLie X.rm k = κ f) (hk' : hL.toLie X.rm k' = κ f') : φ f k' = φ f' k := by
  letI := X.lieModule
  haveI : Module.Invertible (R ⊗[ℤ] 𝓞 F) X.Lie := hX
  have sm : ∀ (r : R) (b : 𝓞 F) (v : X.Lie), (r ⊗ₜ[ℤ] b : R ⊗[ℤ] 𝓞 F) • v = r • b • v := fun _ _ _ ↦ rfl
  haveI : IsScalarTower R (R ⊗[ℤ] 𝓞 F) X.Lie := ⟨fun r s v ↦ by
    induction s with
    | zero => simp
    | add a b ha hb => simp only [smul_add, add_smul, ha, hb]
    | tmul r' b => rw [smul_tmul', sm, sm, smul_assoc]⟩
  have lie : ∀ (s : R ⊗[ℤ] 𝓞 F) x, hL.toLie X.rm (actAlg (dp0 R) (𝟙 _) X.rm s x) = s • hL.toLie X.rm x :=
    fun s x ↦ by
    induction s with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_smul, ha, hb]
    | tmul r b => rw [actAlg_tmul, map_smul, hL.toLie_act, sm]
  have mem : ∀ (s : R ⊗[ℤ] 𝓞 F) (x : Fil X.A), actAlg (dp0 R) (𝟙 _) X.rm s x ∈ Fil X.A := fun s x ↦ by
    have : hL.toLie X.rm x = 0 := LinearMap.mem_ker.1 ((hL.ker_toLie X.rm).ge x.2)
    refine (hL.ker_toLie X.rm).le (LinearMap.mem_ker.2 ?_)
    rw [lie, this, smul_zero]
  let ρ : R ⊗[ℤ] 𝓞 F → Fil X.A → Fil X.A := fun s x ↦ ⟨_, mem s x⟩
  have hρ : ∀ s x, κ (ρ s x) = s • κ x := fun s x ↦ by
    induction s with
    | zero => rw [zero_smul, ← map_zero κ]; exact congrArg κ (Subtype.ext (by simp [ρ]))
    | add a b ha hb =>
      rw [add_smul, ← ha, ← hb, ← map_add]
      exact congrArg κ (Subtype.ext (by simp [ρ]))
    | tmul r b =>
      rw [sm, ← hκ b x (ρ (1 ⊗ₜ b) x) ((actAlg_tmul _ _ _ _ _ _).trans (one_smul _ _)), ← map_smul]
      exact congrArg κ (Subtype.ext (by simp [ρ, actAlg_tmul]))
  refine sub_eq_zero.1 (eq_zero_of_coprime fun l hl ↦ ?_)
  haveI := Fact.mk hl
  obtain ⟨c₀, -, hgen⟩ := FracGen.exists_gen F 𝔠 l
  obtain ⟨m, hm0, hml, hm⟩ := PolPrimeTo.exists_uniform 𝔠 l c₀ hgen
  obtain ⟨n, e, t, τ, hn, cas, tr⟩ := exists_casimir F l R
  obtain ⟨φ₀, hφ₀⟩ := exists_form_of X HR c₀
  obtain ⟨b, hb⟩ := hm c
  obtain ⟨χ, hχ⟩ := exists_form_of X HR ((m : 𝓞 F) • c)
  have eφ : ∀ x y, m • φ x y = φ₀ x (actAlg (dp0 R) (𝟙 _) X.rm (1 ⊗ₜ b) y) := fun x y ↦ by
    rw [actAlg_tmul, one_smul, ← form_smul HR hb hφ₀ hχ, form_smul HR rfl hφ hχ, map_natCast, Module.End.natCast_apply,
      map_nsmul]
  have key := symm_of_casimir e t τ n m cas tr ρ (hL.filToDual X.rm φ₀ (form_fil HR hφ₀))
    (fun s x v ↦ by
      obtain ⟨y, rfl⟩ := hL.toLie_surjective X.rm v
      rw [← lie, hL.filToDual_toLie, hL.filToDual_toLie]
      exact form_balanced HR hφ₀ s x y)
    (fun x hx ↦ Subtype.ext (nsmul_eq_zero_of_radical HR HD hm0 hm hφ₀ fun y ↦ by
      rw [form_skew HR hφ₀, ← hL.filToDual_toLie X.rm φ₀ (form_fil HR hφ₀), hx, LinearMap.zero_apply, neg_zero]))
    κ hρ f (ρ (1 ⊗ₜ b) f')
  rw [hρ, ← hk, ← hk', ← lie, hL.filToDual_toLie, hL.filToDual_toLie, form_balanced HR hφ₀, ← eφ, ← eφ, ← smul_sub,
    ← mul_smul] at key
  exact ⟨_, ((hml.mul_left hn).mul_left hn).mul_left hml, key⟩

end GlobalTheory.KSSymm
