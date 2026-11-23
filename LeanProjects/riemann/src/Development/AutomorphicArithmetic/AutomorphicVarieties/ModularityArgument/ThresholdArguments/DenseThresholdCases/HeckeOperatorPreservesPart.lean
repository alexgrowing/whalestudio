import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TClParts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharOfScalar

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Abs
open TensorProduct
universe u
variable {A K M W ι : Type} [CommRing A] [Field K] [Algebra A K] [AddCommGroup M] [Module A M]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W]
private theorem pa_rho {N : Type} [AddCommGroup N] [Module A N] (s : N →ₗ[A] W)
    (hs : Function.Injective (s.liftBaseChange K)) (E : Submodule K W) (hE : E = Submodule.span K (Set.range s)) :
    ∃ (ρ : Module.End A N →+* Module.End K E) (Ψ : K ⊗[A] N ≃ₗ[K] E),
      (∀ φ v, ρ φ (Ψ v) = Ψ (φ.baseChange K v)) ∧
      (∀ φ f (F : E), (F : W) = s f → (ρ φ F : W) = s (φ f)) ∧
      (∀ (b : A) F, ρ (algebraMap A _ b) F = algebraMap A K b • F) := by
  have hr : LinearMap.range (s.liftBaseChange K) = E := by
    rw [LinearMap.range_liftBaseChange, hE]; rfl
  let Ψ : K ⊗[A] N ≃ₗ[K] E := (LinearEquiv.ofInjective _ hs).trans (LinearEquiv.ofEq _ _ hr)
  have hΨ : ∀ v, (Ψ v : W) = s.liftBaseChange K v := fun v => rfl
  let ρ : Module.End A N →+* Module.End K E :=
    (Ψ.conjRingEquiv : Module.End K (K ⊗[A] N) →+* Module.End K E).comp (Module.End.baseChangeHom A K N).toRingHom
  have h1 : ∀ φ v, ρ φ (Ψ v) = Ψ (φ.baseChange K v) := fun φ v => by
    change Ψ (φ.baseChange K (Ψ.symm (Ψ v))) = _
    rw [Ψ.symm_apply_apply]
  refine ⟨ρ, Ψ, h1, fun φ f F hF => ?_, fun b F => ?_⟩
  · have : F = Ψ (1 ⊗ₜ f) := Subtype.ext (by rw [hF, hΨ]; simp)
    rw [this, h1, hΨ]; simp
  · obtain ⟨v, rfl⟩ := Ψ.surjective F
    rw [h1, ← map_smul, Algebra.algebraMap_eq_smul_one b, LinearMap.baseChange_smul, LinearMap.baseChange_one]
    simp
private theorem pa_ext {N W' : Type} [AddCommGroup N] [Module A N] [AddCommGroup W'] [Module K W'] (s : N →ₗ[A] W)
    (E : Submodule K W) (hE : E = Submodule.span K (Set.range s)) (α β : E →ₗ[K] W')
    (h : ∀ f (F : E), (F : W) = s f → α F = β F) (F : E) : α F = β F := by
  obtain ⟨F, hF⟩ := F
  subst hE
  induction hF using Submodule.span_induction with
  | mem x hx => obtain ⟨f, rfl⟩ := hx; exact h f _ rfl
  | zero => exact (map_zero α).trans (map_zero β).symm
  | add x y hx hy h1 h2 => exact ((map_add α ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])).trans (map_add β ⟨x, hx⟩ ⟨y, hy⟩).symm
  | smul c x hx h1 => exact ((map_smul α c ⟨x, hx⟩).trans (by rw [h1])).trans (map_smul β c ⟨x, hx⟩).symm
private theorem pa_op (Y : Submodule A M) (op : ι → Module.End A M) (s : Y →ₗ[A] W) (opC : ι → Module.End K W)
    (hop : ∀ i (f g : Y), (g : M) = op i f → s g = opC i (s f))
    (E : Submodule K W) (hE : E = Submodule.span K (Set.range s)) (ρ : Module.End A Y →+* Module.End K E)
    (h1 : ∀ φ f (F : E), (F : W) = s f → (ρ φ F : W) = s (φ f)) (i : ι) (t : Module.End A Y) (ht : Restr t (op i))
    (F : E) : (ρ t F : W) = opC i F :=
  pa_ext s E hE (E.subtype ∘ₗ ρ t) (opC i ∘ₗ E.subtype) (fun f F hF => by
    change (ρ t F : W) = opC i F
    rw [h1 t f F hF, hF, hop i f _ (ht f)]) F
private theorem pa_stab (Y : Submodule A M) (op : ι → Module.End A M) (opC : ι → Module.End K W)
    (E : Submodule K W) (ρ : Module.End A Y →+* Module.End K E)
    (h2 : ∀ i t, Restr t (op i) → ∀ F : E, (ρ t F : W) = opC i F)
    (h3 : ∀ (b : A) F, ρ (algebraMap A _ b) F = algebraMap A K b • F)
    (Z : Submodule K W) (hZ : ∀ i, ∀ F ∈ Z ⊓ E, opC i F ∈ Z) (t : Module.End A Y) (ht : t ∈ heckeAlg Y op) :
    ∀ F : E, (F : W) ∈ Z → (ρ t F : W) ∈ Z := by
  induction ht using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, hi⟩ := hx; intro F hF; rw [h2 i x hi]; exact hZ i _ ⟨hF, F.2⟩
  | algebraMap b => intro F hF; rw [h3]; exact Z.smul_mem _ hF
  | add x y _ _ hx hy => intro F hF; rw [map_add]; exact Z.add_mem (hx F hF) (hy F hF)
  | mul x y _ _ hx hy => intro F hF; rw [map_mul]; exact hx _ (hy F hF)
private theorem pa_eig {T E : Type} {J : Type u} [CommRing T] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (act : T →+* Module.End K E) (z : T → K) (Z : J → Submodule K E) (hZ : ⨆ j, Z j = ⊤)
    (hst : ∀ j t, ∀ F ∈ Z j, act t F ∈ Z j) (v : E) (hv : v ≠ 0) (he : ∀ t, act t v = z t • v) :
    ∃ j, ∃ F ∈ Z j, F ≠ 0 ∧ ∀ t, act t F = z t • F := by
  have hc : ∀ s t, Commute (act s) (act t) := fun s t => (Commute.all s t).map act
  obtain ⟨φ, hφ, h⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig (fun t => act t) hc z v hv he
  obtain ⟨j, hj⟩ : ∃ j, φ ∘ₗ (Z j).subtype ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hφ (LinearMap.ker_eq_top.1 (top_le_iff.1 (hZ ▸ iSup_le fun j F hF => ?_)))
    exact LinearMap.congr_fun (hn j) ⟨F, hF⟩
  obtain ⟨F, hF, h'⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot (fun t => (act t).restrict (hst j t))
    (fun s t => LinearMap.ext fun F => Subtype.ext (LinearMap.congr_fun (hc s t).eq F)) z _ hj (fun t F => h t F)
  exact ⟨j, F, F.2, fun h0 => hF (Subtype.ext h0), fun t => congrArg Subtype.val (h' t)⟩
private theorem pa_chr {T E : Type} [CommRing T] [AddCommGroup E] [Module K E]
    (act : T →+* Module.End K E) (Z : Submodule K E) (hZ : Z ≠ ⊥) (h : ∀ t, ∃ μ : K, ∀ F ∈ Z, act t F = μ • F) :
    ∃ z : T →+* K, ∀ t, ∀ F ∈ Z, act t F = z t • F := by
  choose z hz using h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hZ
  have inj : ∀ a b : K, a • v = b • v → a = b := fun a b h => smul_left_injective K hv0 h
  refine ⟨⟨⟨⟨z, inj _ _ ?_⟩, fun s t => inj _ _ ?_⟩, inj _ _ ?_, fun s t => inj _ _ ?_⟩, hz⟩
  · rw [← hz _ v hv]; simp
  · change z (s * t) • v = (z s * z t) • v
    rw [← hz _ v hv, map_mul, Module.End.mul_apply, hz t v hv, map_smul, hz s v hv, smul_smul, mul_comm]
  · change z 0 • v = _
    rw [← hz _ v hv]; simp
  · change z (s + t) • v = (z s + z t) • v
    rw [← hz _ v hv, map_add, LinearMap.add_apply, hz t v hv, hz s v hv, add_smul]
private theorem pa_inst {J : Type u} (Y0 Y : Submodule A M) [Module.Finite A Y] (hle : Y ≤ Y0) (op : ι → Module.End A M)
    [hc : Fact (CommOn Y op)] (e : Module.End A Y0) (he : e ∈ heckeAlg Y0 op)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y)
    (s : Y0 →ₗ[A] W) (hs : Function.Injective (s.liftBaseChange K)) (opC : ι → Module.End K W)
    (hop : ∀ i (f g : Y0), (g : M) = op i f → s g = opC i (s f))
    (O E : Submodule K W) (hO : O = Submodule.span K (Set.range s))
    (hE : E = Submodule.span K (Set.range (s ∘ₗ Submodule.inclusion hle)))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∀ F ∈ Z j, opC i F ∈ Z j) (hOZ : O = ⨆ j, Z j ⊓ O) :
    E = ⨆ j, Z j ⊓ E ∧ ∃ act : heckeAlg Y op →+* Module.End K E,
      (∀ (t : heckeAlg Y op) (f : Y) (F : E), (F : W) = s (Submodule.inclusion hle f) →
        (act t F : W) = s (Submodule.inclusion hle ((t : Module.End A Y) f))) ∧
      (∀ i (F : E), (act (heckeGen Y op i) F : W) = opC i F) ∧
      (∀ (b : A) (F : E), act (algebraMap A _ b) F = algebraMap A K b • F) ∧
      (∀ z : heckeAlg Y op →+* K, z.comp (algebraMap A _) = algebraMap A K →
        ∃ j F, F ≠ 0 ∧ F ∈ Z j ⊓ E ∧ ∀ i, opC i F = z (heckeGen Y op i) • F) ∧
      (∀ Z' : Submodule K W, Z' ⊓ E ≠ ⊥ → (∀ i, ∃ μ : K, ∀ F ∈ Z' ⊓ E, opC i F = μ • F) →
        ∃ z : heckeAlg Y op →+* K, z.comp (algebraMap A _) = algebraMap A K ∧
          ∀ t (F : E), (F : W) ∈ Z' → act t F = z t • F) := by
  have heY : ∀ y : Y0, (e y : M) ∈ Y := fun y => (hY _).2 (LinearMap.congr_fun hi.eq y)
  let r : Y0 →ₗ[A] Y := LinearMap.codRestrict _ (Y0.subtype ∘ₗ e) heY
  have hr : r ∘ₗ Submodule.inclusion hle = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (congrArg (fun z : Y0 => (z : M)) ((hY (Submodule.inclusion hle y)).1 y.2))
  have hs' : Function.Injective ((s ∘ₗ Submodule.inclusion hle).liftBaseChange K) := by
    have h1 : (s ∘ₗ Submodule.inclusion hle).liftBaseChange K =
        s.liftBaseChange K ∘ₗ (Submodule.inclusion hle).baseChange K := by
      ext y; simp
    rw [h1, LinearMap.coe_comp]
    refine hs.comp (Function.LeftInverse.injective (g := r.baseChange K) fun v => ?_)
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id, LinearMap.id_apply]
  obtain ⟨ρ0, -, -, a1, a3⟩ := pa_rho s hs O hO
  obtain ⟨ρ, Ψ, b0, b1, b3⟩ := pa_rho _ hs' E hE
  have a2 := pa_op Y0 op s opC hop O hO ρ0 a1
  have b2 := pa_op Y op (s ∘ₗ Submodule.inclusion hle) opC (fun i f g h => hop i _ _ h) E hE ρ b1
  have hEO : E ≤ O := by
    rw [hE, hO]; exact Submodule.span_mono (by rintro _ ⟨f, rfl⟩; exact ⟨_, rfl⟩)
  have hfix : ∀ F : E, (ρ0 e ⟨F, hEO F.2⟩ : W) = F :=
    pa_ext _ E hE (O.subtype ∘ₗ ρ0 e ∘ₗ Submodule.inclusion hEO) E.subtype fun f F hF => by
      change (ρ0 e ⟨F, hEO F.2⟩ : W) = F
      rw [a1 e (Submodule.inclusion hle f) _ hF, hF, (hY (Submodule.inclusion hle f)).1 f.2]
      rfl
  have hin : ∀ F : O, (ρ0 e F : W) ∈ E := fun F =>
    (Submodule.Quotient.mk_eq_zero E).1 (pa_ext s O hO (E.mkQ ∘ₗ O.subtype ∘ₗ ρ0 e) 0 (fun f F hF => by
      change E.mkQ (ρ0 e F : W) = 0
      rw [a1 e f _ hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hE]
      exact Submodule.subset_span ⟨r f, rfl⟩) F)
  have hsum : E = ⨆ j, Z j ⊓ E := by
    refine le_antisymm (fun F hF => ?_) (iSup_le fun j => inf_le_right)
    have key : ∀ G ∈ ⨆ j, Z j ⊓ O, ∃ h : G ∈ O, (ρ0 e ⟨G, h⟩ : W) ∈ ⨆ j, Z j ⊓ E := by
      intro G hG
      induction hG using Submodule.iSup_induction' with
      | mem j G hG =>
        exact ⟨hG.2, Submodule.mem_iSup_of_mem j
          ⟨pa_stab Y0 op opC O ρ0 a2 a3 (Z j) (fun i F hF => hZ j i F hF.1) e he _ hG.1, hin _⟩⟩
      | zero => exact ⟨zero_mem _, by rw [show (⟨0, zero_mem _⟩ : O) = 0 from rfl, map_zero]; exact zero_mem _⟩
      | add x y _ _ hx hy =>
        obtain ⟨hx, hx'⟩ := hx
        obtain ⟨hy, hy'⟩ := hy
        exact ⟨add_mem hx hy, by
          rw [show (⟨x + y, add_mem hx hy⟩ : O) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]; exact add_mem hx' hy'⟩
    obtain ⟨h, h'⟩ := key F (hOZ ▸ hEO hF)
    rwa [show (ρ0 e ⟨F, h⟩ : W) = F from hfix ⟨F, hF⟩] at h'
  let act : heckeAlg Y op →+* Module.End K E := ρ.comp (heckeAlg Y op).val.toRingHom
  have c2 : ∀ i (F : E), (act (heckeGen Y op i) F : W) = opC i F := fun i F => b2 i _ (fun _ => rfl) F
  refine ⟨hsum, act, fun t f F hF => b1 t f F hF, c2, b3, fun z hz => ?_, fun Z' h0 hsc => ?_⟩
  · haveI : FiniteDimensional K E := Module.Finite.equiv Ψ
    obtain ⟨v, hv, hv'⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig (M := Y)
      ({ z with commutes' := fun b => RingHom.congr_fun hz b } : heckeAlg Y op →ₐ[A] K)
    have htop : ⨆ j, (Z j).comap E.subtype = ⊤ := by
      apply Submodule.map_injective_of_injective E.subtype_injective
      rw [Submodule.map_iSup, Submodule.map_subtype_top]
      simp_rw [Submodule.map_comap_subtype, inf_comm E]
      exact hsum.symm
    obtain ⟨j, F, hF, hF0, hF'⟩ := pa_eig act z (fun j => (Z j).comap E.subtype) htop
      (fun j t F hF => pa_stab Y op opC E ρ b2 b3 (Z j) (fun i F hF => hZ j i F hF.1) t t.2 F hF) (Ψ v)
      (fun h => hv (Ψ.map_eq_zero_iff.1 h)) (fun t => (b0 t v).trans (by rw [← map_smul]; exact congrArg Ψ (hv' t)))
    exact ⟨j, F, fun h => hF0 (Subtype.ext h), ⟨hF, F.2⟩, fun i => by rw [← c2, hF']; rfl⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h0
    obtain ⟨z, hz⟩ := pa_chr act (Z'.comap E.subtype)
      ((Submodule.ne_bot_iff _).2 ⟨⟨v, hv.2⟩, hv.1, fun h => hv0 (congrArg Subtype.val h)⟩) (by
        rintro ⟨t, ht⟩
        change ∃ μ : K, ∀ F ∈ Z'.comap E.subtype, ρ t F = μ • F
        induction ht using Algebra.adjoin_induction with
        | mem x hx =>
          obtain ⟨i, hi⟩ := hx
          obtain ⟨μ, hμ⟩ := hsc i
          exact ⟨μ, fun F hF => Subtype.ext ((b2 i x hi F).trans (hμ F ⟨hF, F.2⟩))⟩
        | algebraMap b => exact ⟨_, fun F _ => b3 b F⟩
        | add x y _ _ hx hy =>
          obtain ⟨μ, hμ⟩ := hx
          obtain ⟨ν, hν⟩ := hy
          exact ⟨μ + ν, fun F hF => by rw [map_add, LinearMap.add_apply, hμ F hF, hν F hF, add_smul]⟩
        | mul x y _ _ hx hy =>
          obtain ⟨μ, hμ⟩ := hx
          obtain ⟨ν, hν⟩ := hy
          exact ⟨ν * μ, fun F hF => by rw [map_mul, Module.End.mul_apply, hν F hF, map_smul, hμ F hF, smul_smul]⟩)
    refine ⟨z, RingHom.ext fun b => ?_, fun t F hF => hz t F hF⟩
    refine smul_left_injective K (m := (⟨v, hv.2⟩ : E)) (fun h => hv0 (congrArg Subtype.val h)) ?_
    exact (hz _ ⟨v, hv.2⟩ hv.1).symm.trans (b3 b _)
end Abs
universe u in
private theorem pa_main {A K M W ι : Type} [CommRing A] [Field K] [AddCommGroup M] [Module A M]
    [AddCommGroup W] [Module K W] {J : Type u} (Y0 Y : Submodule A M) [Module.Free A Y0] [Module.Finite A Y] (hle : Y ≤ Y0)
    (op : ι → Module.End A M)
    [hc : Fact (CommOn Y op)] (e : Module.End A Y0) (he : e ∈ heckeAlg Y0 op)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y) (χ : A →+* K) (sp : M → W)
    (hadd : ∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y0, ∀ b : A, sp (b • f) = χ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y0, sp (op i f) = opC i (sp f))
    (O E : Submodule K W) (hO : Submodule.span K (sp '' Y0) = O) (hE : E = Submodule.span K (sp '' Y))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∀ F ∈ Z j, opC i F ∈ Z j) (hOZ : O = ⨆ j, Z j ⊓ O) :
    E ≤ O ∧ E = ⨆ j, Z j ⊓ E ∧ ∃ act : heckeAlg Y op →+* Module.End K E,
      (∀ (t : heckeAlg Y op) (f : Y) (F : E), (F : W) = sp f → (act t F : W) = sp ((t : Module.End A Y) f : Y)) ∧
      (∀ i (F : E), (act (heckeGen Y op i) F : W) = opC i F) ∧
      (∀ (b : A) (F : E), act (algebraMap A _ b) F = χ b • F) ∧
      (∀ z : heckeAlg Y op →+* K, z.comp (algebraMap A _) = χ →
        ∃ j F, F ≠ 0 ∧ F ∈ Z j ⊓ E ∧ ∀ i, opC i F = z (heckeGen Y op i) • F) ∧
      (∀ Z' : Submodule K W, Z' ⊓ E ≠ ⊥ → (∀ i, ∃ μ : K, ∀ F ∈ Z' ⊓ E, opC i F = μ • F) →
        ∃ z : heckeAlg Y op →+* K, z.comp (algebraMap A _) = χ ∧
          ∀ t (F : E), (F : W) ∈ Z' → act t F = z t • F) := by
  letI : Algebra A K := χ.toAlgebra
  letI : Module A W := Module.compHom W χ
  haveI : IsScalarTower A K W := ⟨fun a k w => mul_smul (χ a) k w⟩
  let s : Y0 →ₗ[A] W :=
    { toFun := fun f => sp f
      map_add' := fun f g => hadd _ f.2 _ g.2
      map_smul' := fun b f => hsmul _ f.2 b }
  refine ⟨hE ▸ hO ▸ Submodule.span_mono (Set.image_mono hle),
    pa_inst Y0 Y hle op e he hi hY s ?_ opC (fun i f g h => ?_) O E ?_ ?_ Z hZ hOZ⟩
  · let b := Module.Free.chooseBasis A Y0
    have h1 : s.liftBaseChange K = Finsupp.linearCombination K (fun i => sp (b i)) ∘ₗ (b.baseChange K).repr.toLinearMap :=
      (b.baseChange K).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.linearCombination_single,
          Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
        rfl
    rw [h1, LinearMap.coe_comp]
    exact Function.Injective.comp (hind _ b) (b.baseChange K).repr.injective
  · change sp g = opC i (sp f)
    rw [h, hop i _ f.2]
  · rw [← hO, Set.image_eq_range]; rfl
  · rw [hE, Set.image_eq_range]; rfl
private theorem pa_pt {O A T K K' : Type} [CommRing O] [CommRing A] [CommRing T] [Field K] [Field K'] [Algebra O A]
    [Algebra O T] [Algebra A T] [IsScalarTower O A T] [Algebra O K] (ι : K ≃+* K') (x : A →ₐ[O] K) (z : T →+* K')
    (hz : z.comp (algebraMap A T) = ι.toRingHom.comp x.toRingHom) :
    ∃ y : T →ₐ[O] K, y.toRingHom.comp (algebraMap A T) = x.toRingHom ∧ ∀ t, ι (y t) = z t := by
  have hz' : ∀ b, ι.symm (z (algebraMap A T b)) = x b := fun b => ι.symm_apply_eq.2 (RingHom.congr_fun hz b)
  refine ⟨{ ι.symm.toRingHom.comp z with commutes' := fun b => ?_ }, RingHom.ext hz', fun t => ι.apply_symm_apply _⟩
  exact (congrArg (fun t => ι.symm (z t)) (IsScalarTower.algebraMap_apply O A T b)).trans ((hz' _).trans (x.commutes b))
universe u in
private theorem pa_fin {R A K K' M W ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Field K'] [Algebra R K']
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup W] [Module K W] {J : Type u} (Y0 Y : Submodule A M) [Module.Free A Y0] [Module.Finite A Y] (hle : Y ≤ Y0)
    (op : ι → Module.End A M)
    [hc : Fact (CommOn Y op)] (e : Module.End A Y0) (he : e ∈ heckeAlg Y0 op)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y) (φ : K' ≃+* K) (x : A →ₐ[R] K') (sp : M → W)
    (hadd : ∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y0, ∀ b : A, sp (b • f) = φ (x b) • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y0, sp (op i f) = opC i (sp f))
    (O E : Submodule K W) (hO : Submodule.span K (sp '' Y0) = O) (hE : E = Submodule.span K (sp '' Y))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∀ F ∈ Z j, opC i F ∈ Z j) (hOZ : O = ⨆ j, Z j ⊓ O) :
    E ≤ O ∧ E = ⨆ j, Z j ⊓ E ∧ ∃ act : heckeAlg Y op →+* Module.End K E,
      (∀ (t : heckeAlg Y op) (f : Y) (F : E), (F : W) = sp f → (act t F : W) = sp ((t : Module.End A Y) f : Y)) ∧
      (∀ i (F : E), (act (heckeGen Y op i) F : W) = opC i F) ∧
      (∀ (b : A) (F : E), act (algebraMap A _ b) F = φ (x b) • F) ∧
      (∀ y : heckeAlg Y op →ₐ[R] K', y.toRingHom.comp (algebraMap A _) = x.toRingHom →
        ∃ j F, F ≠ 0 ∧ F ∈ Z j ⊓ O ∧ ∀ i, opC i F = φ (y (heckeGen Y op i)) • F) ∧
      (∀ Z' : Submodule K W, Z' ⊓ E ≠ ⊥ → (∀ i, ∃ μ : K, ∀ F ∈ Z' ⊓ O, opC i F = μ • F) →
        ∃ y : heckeAlg Y op →ₐ[R] K', y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧
          ∀ t (F : E), (F : W) ∈ Z' → act t F = φ (y t) • F) := by
  obtain ⟨hEO, hsum, act, h1, h2, h3, h4, h5⟩ := pa_main Y0 Y hle op e he hi hY (φ.toRingHom.comp x.toRingHom) sp hadd
    hsmul hind opC hop O E hO hE Z hZ hOZ
  refine ⟨hEO, hsum, act, h1, h2, h3, fun y hy => ?_, fun Z' hne hsc => ?_⟩
  · obtain ⟨j, F, hF0, hF, h⟩ := h4 (φ.toRingHom.comp y.toRingHom) (by rw [RingHom.comp_assoc, hy])
    exact ⟨j, F, hF0, ⟨hF.1, hEO hF.2⟩, h⟩
  · obtain ⟨z, hz, h⟩ := h5 Z' hne fun i => (hsc i).imp fun μ hμ F hF => hμ F ⟨hF.1, hEO hF.2⟩
    obtain ⟨y, hy, hy'⟩ := pa_pt φ x z hz
    exact ⟨y, hy, fun t F hF => by rw [hy', h t F hF]⟩
private theorem pa_iso {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ H M} {Y : Submodule ℂ M} {σ : SmIrr H} (h : IsoSum ρ Y σ) (g : H) : ∀ F ∈ Y, ρ g F ∈ Y := by
  intro F hF
  refine (iSup_le (a := Y.comap (ρ g)) ?_) (h hF)
  rintro f _ ⟨v, rfl⟩
  change ρ g (f.1 v) ∈ Y
  rw [← f.2.1]
  exact f.2.2 ⟨_, rfl⟩
private theorem pa_pi {V M : Type} [Finite V] [DecidableEq V] {G : V → Type} [∀ v, Group (G v)] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (∀ v, G v) M) (Y : Submodule ℂ M) (h : ∀ v g, ∀ F ∈ Y, ρ (Pi.mulSingle v g) F ∈ Y)
    (g : ∀ v, G v) : ∀ F ∈ Y, ρ g F ∈ Y := by
  let S : Subgroup (∀ v, G v) :=
    { carrier := {g | (∀ F ∈ Y, ρ g F ∈ Y) ∧ ∀ F ∈ Y, ρ g⁻¹ F ∈ Y}
      mul_mem' := fun {a b} ha hb => ⟨fun F hF => by rw [map_mul]; exact ha.1 _ (hb.1 F hF),
        fun F hF => by rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 F hF)⟩
      one_mem' := ⟨fun F hF => by rw [map_one]; exact hF, fun F hF => by rw [inv_one, map_one]; exact hF⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  exact (Subgroup.pi_mem_of_mulSingle_mem (H := S) g fun v =>
    ⟨h v _, by rw [← Pi.mulSingle_inv]; exact h v _⟩).1
theorem hecke_operator_preserves_part {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d : ℕ}
    (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ) (i : H.Op) : ∀ F ∈ Y.Y, H.opC ι lam d i F ∈ Y.Y := by
  classical
  have h1 : ∀ g : GV n H.Sl, ∀ F ∈ Y.Y, H.X.rpF ℂ d H.m g F ∈ Y.Y := by
    exact pa_pi _ _ fun v g => pa_iso (Y.isoL v) g
  intro F hF
  rcases i with x | x
  · change sphOp (H.atW ι d x.1.1) (x.2 + 1) F ∈ _
    rw [Y.sph x.1 _ F hF]
    exact Y.Y.smul_mem _ hF
  · refine Y.Y.smul_mem _ ?_
    exact finsum_induction (p := fun φ : Module.End ℂ (Fin H.m → H.X.Fn ℂ d) => φ F ∈ Y.Y) (zero_mem _)
      (fun _ _ => add_mem) fun q => h1 _ F hF
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Hi.partAct0_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    lam ∈ H.admitted → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ E : Submodule ℂ (Fin H.m → H.X.Fn ℂ d), E = Submodule.span ℂ (sp '' H.MK θ a K) → (E = ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r}, Y.1.Y ⊓ E ∨ ¬ H.Good θ x.toRingHom lam) ∧ ∃ act : H.TK θ a K →+* Module.End ℂ E, (∀ (t : H.TK θ a K) (f : H.MK θ a K) (F : E), (F : Fin H.m → H.X.Fn ℂ d) = sp f → (act t F : Fin H.m → H.X.Fn ℂ d) = sp ((t : Module.End A (H.MK θ a K)) f : H.MK θ a K)) ∧ (∀ i (F : E), (act (H.gen θ a K i) F : Fin H.m → H.X.Fn ℂ d) = H.opC ι lam d i F) ∧ (∀ (b : A) (F : E), act (algebraMap A _ b) F = ι (x b) • F) ∧ (∀ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom → ∃ (Y : H.PartAltAlt ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d) (e : ℕ), P lam Y.r ∧ c0 ≤ e ∧ F ≠ 0 ∧ F ∈ Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K e ∧ ∀ i, H.opC ι lam d i F = ι (y (H.gen θ a K i)) • F) ∧ (H.Good θ x.toRingHom lam → ∀ Y : H.PartAltAlt ι lam ξ, Y.Y ⊓ E ≠ ⊥ → ∃ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧ ∀ t (F : E), (F : Fin H.m → H.X.Fn ℂ d) ∈ Y.Y → act t F = ι (y t) • F) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ E hE
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := IsCNL.finite
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, hK⟩ := hiComm L Ω l n c H hH A θ hθ K
  haveI := (hK a).2.1
  obtain ⟨e, he, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨hEO, hsum, act, h1, h2, h3, h4, h5⟩ := pa_fin (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A)
    e he hi hY ι x sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    _ E (hsp.span K c0 le_rfl) hE (fun Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r} => Y.1.Y)
    (fun Y => _root_.hecke_operator_preserves_part H ι lam ξ Y.1) (_root_.UpperTheory.V.Hi.clParts_alt L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2
  refine ⟨Or.inl hsum, act, h1, h2, h3, fun y hy => ?_, fun hg Y hne => ?_⟩
  · obtain ⟨Y, F, hF0, hF, h⟩ := h4 y hy
    exact ⟨Y.1, F, c0, Y.2, le_rfl, hF0, hF, h⟩
  · obtain ⟨ω, -, -, -, hω⟩ := _root_.UpperTheory.V.Hi.goodScalB_alt hN L Ω l n c H hH A θ hθ ι x lam d ξ c0 sp hsp hg Y K c0 le_rfl
      (fun h => hne (le_bot_iff.1 ((inf_le_inf_left _ hEO).trans h.le)))
    refine h5 Y.Y hne ?_
    rintro (i | i)
    · exact ⟨_, fun F hF => Y.sph i.1 _ F hF.1⟩
    · exact ⟨_, (hω i.1 i.2).2⟩
end
