import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemma
import GroundTheory.AutomorphicForms.LeviStagesProduct
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β δ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem subsingleton_innerJacquetSpace_of_isCuspidal {σ : Representation ℂ (levi F n β) W}
    (hc : IsCuspidal σ) {w : Equiv.Perm (Fin n)}
    (h : ¬ ∀ a b, β (w a) = β (w b) → δ a = δ b) : Subsingleton (innerJacquetSpace β δ w σ) := by
  push Not at h
  obtain ⟨a, b, hab, hne⟩ := h
  exact hc (δ ∘ ⇑w⁻¹) ⟨w a, w b, hab, by simpa using hne⟩

theorem subsingleton_indSpace {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
    {U : Type*} [AddCommGroup U] [Module ℂ U] [Subsingleton U] (ρ : Representation ℂ H U) :
    Subsingleton (indSpace H ρ) :=
  ⟨fun _ _ => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩

theorem subsingleton_piece_of_isCuspidal {σ : Representation ℂ (levi F n β) W}
    (hc : IsCuspidal σ) {w : Equiv.Perm (Fin n)}
    (h : ¬ ∀ a b, β (w a) = β (w b) → δ a = δ b) :
    Subsingleton (indSpace (cellLeviSub F β δ w) (normInducing σ δ w)) :=
  haveI := subsingleton_innerJacquetSpace_of_isCuspidal hc h
  subsingleton_indSpace _ _

section Conj

variable {w : Equiv.Perm (Fin n)}

theorem permGL_conj_mem_levi (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) {m : GL (Fin n) F}
    (hm : m ∈ levi F n δ) : permGL F w * m * (permGL F w)⁻¹ ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  rw [permGL_conj_apply]
  refine (mem_levi.1 hm) _ _ fun e => hij ?_
  simpa using (h _ _).1 e

theorem permGL_inv_conj_mem_levi (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) {m : GL (Fin n) F}
    (hm : m ∈ levi F n β) : (permGL F w)⁻¹ * m * permGL F w ∈ levi F n δ := by
  rw [mem_levi]
  intro i j hij
  have e1 : (permGL F w)⁻¹ * m * permGL F w =
      permGL F w⁻¹ * m * (permGL F w⁻¹)⁻¹ := by
    rw [map_inv, inv_inv]
  rw [e1, permGL_conj_apply, inv_inv]
  exact (mem_levi.1 hm) _ _ fun e => hij ((h _ _).2 e)

def leviConj (w : Equiv.Perm (Fin n)) (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) :
    levi F n δ ≃ₜ* levi F n β where
  toFun m := ⟨permGL F w * m * (permGL F w)⁻¹, permGL_conj_mem_levi h m.2⟩
  invFun m := ⟨(permGL F w)⁻¹ * m * permGL F w, permGL_inv_conj_mem_levi h m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' m m' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul
    continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul
    continuous_const).subtype_mk _

theorem coe_leviConj (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) (m : levi F n δ) :
    ((leviConj w h m : levi F n β) : GL (Fin n) F) = permGL F w * m * (permGL F w)⁻¹ :=
  rfl

end Conj

section Matching

open MeasureTheory Measure

variable {w : Equiv.Perm (Fin n)}

theorem mem_cellLeviSub (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) (m : levi F n δ) :
    m ∈ cellLeviSub F β δ w := by
  refine Subgroup.mem_subgroupOf.2 ⟨m.2, fun i j hij => ?_⟩
  refine (mem_levi.1 m.2) i j fun e => ?_
  have := (h i j).1 e
  simp only [Function.comp_apply] at hij
  rw [this] at hij
  exact lt_irrefl _ hij

theorem leviUnipotent_eq_one (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b))
    (u : leviUnipotent F n β (δ ∘ ⇑w⁻¹)) : (u : levi F n β) = 1 := by
  have hu : (((u : levi F n β) : GL (Fin n) F)) ∈ unipotentRadical F n (δ ∘ ⇑w⁻¹) :=
    Subgroup.mem_subgroupOf.1 u.2
  obtain ⟨-, hu1⟩ := mem_unipotentRadical.1 hu
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  by_cases hb : β i = β j
  · exact hu1 i j ((h (w⁻¹ i) (w⁻¹ j)).2 (by simpa using hb))
  · have hij : i ≠ j := fun e => hb (e ▸ rfl)
    rw [(mem_levi.1 (u : levi F n β).2) i j hb]
    simp [Matrix.one_apply_ne hij]

theorem innerMk_injective (σ : Representation ℂ (levi F n β) W)
    (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) :
    Function.Injective
      (Representation.Coinvariants.mk (σ.comp (leviUnipotent F n β (δ ∘ ⇑w⁻¹)).subtype)) := by
  intro x y hxy
  rw [Representation.Coinvariants.mk_eq_iff] at hxy
  have hker : Representation.Coinvariants.ker
      (σ.comp (leviUnipotent F n β (δ ∘ ⇑w⁻¹)).subtype) = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨⟨u, v⟩, rfl⟩
    simp [leviUnipotent_eq_one h u]
  rw [hker] at hxy
  exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hxy)

def innerEquiv (σ : Representation ℂ (levi F n β) W) (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) :
    W ≃ₗ[ℂ] innerJacquetSpace β δ w σ :=
  LinearEquiv.ofBijective (Representation.Coinvariants.mk _)
    ⟨innerMk_injective σ h, Representation.Coinvariants.mk_surjective _⟩

theorem innerEquiv_apply (σ : Representation ℂ (levi F n β) W)
    (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) (v : W) :
    innerEquiv σ h v = Representation.Coinvariants.mk _ v :=
  rfl

theorem permConj_mem_integralGL (w : Equiv.Perm (Fin n)) {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    permGL F w * k * (permGL F w)⁻¹ ∈ integralGL F n :=
  (integralGL F n).mul_mem ((integralGL F n).mul_mem (permGL_mem_integralGL w) hk)
    ((integralGL F n).inv_mem (permGL_mem_integralGL w))

theorem normScalarHom_eq_one (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) :
    normScalarHom F β δ w = 1 := by
  ext b
  obtain ⟨μ, hμ⟩ := exists_diagPow_eq (γ := δ) (δ := β ∘ w) b
  rw [hμ (normScalarHom F β δ w) fun k hk => ?_, hμ (1 : leviPar F n δ (β ∘ w) →* ℂ)
    fun _ _ => rfl]
  · have hA := modularCharacter_leviPar_diagPow (F := F) (γ := δ) (δ := β ∘ w) μ
    have hB := modularCharacter_cellInnerHom_diagPow (F := F) (β := β) (γ := δ) (w := w) μ
    have hA1 : ∏ s : {ij : Fin n × Fin n // δ ij.1 = δ ij.2 ∧ (β ∘ w) ij.1 < (β ∘ w) ij.2},
        Measures.modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
          Measures.modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) = 1 :=
      Finset.prod_eq_one fun s _ => absurd s.2.2 (by
        rw [show (β ∘ w) s.1.1 = (β ∘ w) s.1.2 from (h _ _).1 s.2.1]
        exact lt_irrefl _)
    have hB1 : ∏ s : {p : Fin n × Fin n // (β ∘ w) p.1 = (β ∘ w) p.2 ∧ δ p.1 < δ p.2},
        Measures.modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
          Measures.modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) = 1 :=
      Finset.prod_eq_one fun s _ => absurd s.2.2 (by
        rw [show δ s.1.1 = δ s.1.2 from (h _ _).2 s.2.1]
        exact lt_irrefl _)
    rw [hA1] at hA
    rw [hB1] at hB
    show ((NNReal.sqrt (modularCharacter (⟨Cartan.diagPow F n μ, diagPow_mem_leviPar μ⟩ :
        leviPar F n δ (β ∘ w))) : ℝ) : ℂ) *
      (((NNReal.sqrt (modularCharacter (cellInnerHom β δ w ⟨Cartan.diagPow F n μ,
        diagPow_mem_levi μ, diagPow_mem_blockUpper' (β ∘ w) μ⟩)) : ℝ) : ℂ))⁻¹ = 1
    rw [hA, hB]
    simp
  · change normLeviParSqrtModular F δ (β ∘ w) k *
      (normLeviParSqrtModular F β (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w k))⁻¹ = 1
    rw [normLeviParSqrtModular_eq_one hk, normLeviParSqrtModular_eq_one
      (leviProj_mem_integralGL (p := permConj F β w
        (Subgroup.inclusion cellLeviParabolic_le_blockUpper k))
          (permConj_mem_integralGL w hk))]
    simp

theorem normInducing_eq_levJacquetAction (σ : Representation ℂ (levi F n β) W)
    (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) (b : cellLeviSub F β δ w)
    (x : innerJacquetSpace β δ w σ) :
    normInducing σ δ w b x =
      levJacquetAction β σ (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b)) x := by
  have h1 := congrArg (fun ψ : leviPar F n δ (β ∘ w) →* ℂ => ψ (cellLeviSubIncl F β δ w b))
    (normScalarHom_eq_one (F := F) h)
  have h2 : normLeviParSqrtModular F δ (β ∘ w) (cellLeviSubIncl F β δ w b) *
      normLeviParInvSqrtModular F β (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b)) =
      1 := h1
  change normLeviParSqrtModular F δ (β ∘ w) (cellLeviSubIncl F β δ w b) •
    (normLeviParInvSqrtModular F β (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b)) •
      levJacquetAction β σ (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b)) x) = _
  rw [smul_smul, h2, one_smul]

theorem leviInfIncl_cellInnerHom (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b))
    (b : cellLeviSub F β δ w) :
    leviInfIncl β (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b)) =
      leviConj w h (b : levi F n δ) := by
  apply Subtype.ext
  have hm := permGL_conj_mem_levi h (b : levi F n δ).2
  have e1 : permConj F β w (Subgroup.inclusion cellLeviParabolic_le_blockUpper
      (cellLeviSubIncl F β δ w b)) = ⟨_, levi_le_blockUpper hm⟩ := Subtype.ext rfl
  show ((leviProj F n β (permConj F β w (Subgroup.inclusion cellLeviParabolic_le_blockUpper
      (cellLeviSubIncl F β δ w b))) : levi F n β) : GL (Fin n) F) = _
  rw [e1, leviProj_of_mem_levi hm]
  rfl

theorem piece_apply_eq (σ : Representation ℂ (levi F n β) W)
    (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b))
    (f : indSpace (cellLeviSub F β δ w) (normInducing σ δ w)) (g : levi F n δ) :
    (f : levi F n δ → innerJacquetSpace β δ w σ) g =
      innerEquiv σ h (σ (leviConj w h g)
        ((innerEquiv σ h).symm ((f : levi F n δ → innerJacquetSpace β δ w σ) 1))) := by
  have hf := ((mem_indSpace).1 f.2).1 ⟨g, mem_cellLeviSub h g⟩ 1
  rw [mul_one] at hf
  change (f : levi F n δ → innerJacquetSpace β δ w σ) g = _ at hf
  rw [hf, normInducing_eq_levJacquetAction σ h]
  conv_lhs => rw [← (innerEquiv σ h).apply_symm_apply
    ((f : levi F n δ → innerJacquetSpace β δ w σ) 1)]
  rw [innerEquiv_apply, innerEquiv_apply, levJacquetAction_mk, leviInfIncl_cellInnerHom h]

variable (w) in

def pieceEval (σ : Representation ℂ (levi F n β) W) (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) :
    Representation.IntertwiningMap (indRep (cellLeviSub F β δ w) (normInducing σ δ w))
      (σ.comp (leviConj w h).toMulEquiv.toMonoidHom) where
  toLinearMap := (innerEquiv σ h).symm.toLinearMap ∘ₗ
    evalOne (cellLeviSub F β δ w) (normInducing σ δ w)
  isIntertwining' g := LinearMap.ext fun f => by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, evalOne_apply]
    rw [coe_indRep_apply, one_mul, piece_apply_eq σ h f g, LinearEquiv.symm_apply_apply]
    rfl

theorem pieceEval_apply (σ : Representation ℂ (levi F n β) W)
    (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b))
    (f : indSpace (cellLeviSub F β δ w) (normInducing σ δ w)) :
    pieceEval w σ h f =
      (innerEquiv σ h).symm ((f : levi F n δ → innerJacquetSpace β δ w σ) 1) :=
  rfl

theorem exists_bijective_piece {σ : Representation ℂ (levi F n β) W} (hσ : IsSmooth σ)
    (w : Equiv.Perm (Fin n)) (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) :
    ∃ e : Representation.IntertwiningMap (indRep (cellLeviSub F β δ w) (normInducing σ δ w))
      (σ.comp (leviConj w h).toMulEquiv.toMonoidHom), Function.Bijective e := by
  refine ⟨pieceEval w σ h, fun f₁ f₂ he => ?_, fun v => ?_⟩
  · rw [pieceEval_apply, pieceEval_apply] at he
    exact Subtype.ext (funext fun g => by rw [piece_apply_eq σ h f₁ g, piece_apply_eq σ h f₂ g, he])
  ·
    let φ : levi F n δ → innerJacquetSpace β δ w σ := fun g => innerEquiv σ h (σ (leviConj w h g) v)
    have hφ : φ ∈ indSpace (cellLeviSub F β δ w) (normInducing σ δ w) := by
      refine ⟨fun b g => ?_, ?_⟩
      · simp only [φ]
        rw [normInducing_eq_levJacquetAction σ h, innerEquiv_apply, innerEquiv_apply,
          levJacquetAction_mk, leviInfIncl_cellInnerHom h, map_mul, map_mul, Module.End.mul_apply]
      · refine ⟨(stabilizerOf σ v).comap (leviConj w h).toMulEquiv.toMonoidHom, ?_,
          fun k hk g => ?_⟩
        · rw [Subgroup.coe_comap]
          exact (hσ v).preimage (leviConj w h).continuous
        · simp only [φ]
          rw [map_mul, map_mul, Module.End.mul_apply]
          rw [Subgroup.mem_comap, mem_stabilizerOf] at hk
          rw [show σ ((leviConj w h) k) v = v from hk]
    refine ⟨⟨φ, hφ⟩, ?_⟩
    rw [pieceEval_apply]
    show (innerEquiv σ h).symm (innerEquiv σ h (σ (leviConj w h 1) v)) = v
    rw [LinearEquiv.symm_apply_apply, map_one, map_one, Module.End.one_apply]

theorem isIrreducible_of_bijective {G : Type*} [Group G] {V U : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G U} (e : Representation.IntertwiningMap ρ ρ')
    (he : Function.Bijective e) [ρ'.IsIrreducible] : ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have : IsSimpleModule (MonoidAlgebra ℂ G) ρ'.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ').1 inferInstance
  exact IsSimpleModule.congr (LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ' e) he)

theorem isIrreducible_piece {σ : Representation ℂ (levi F n β) W} [σ.IsIrreducible]
    (hσ : IsSmooth σ) (w : Equiv.Perm (Fin n)) (h : ∀ a b, δ a = δ b ↔ β (w a) = β (w b)) :
    (indRep (cellLeviSub F β δ w) (normInducing σ δ w)).IsIrreducible := by
  obtain ⟨e, he⟩ := exists_bijective_piece hσ w h
  have : Representation.IsIrreducible (σ.comp (leviConj w h).toMulEquiv.toMonoidHom) :=
    (isIrreducible_comp_iff (leviConj w h) σ).2 inferInstance
  exact isIrreducible_of_bijective e he

end Matching

section Count

theorem card_image_le_of_imp {ι : Type*} [Fintype ι] {f g : ι → ℕ}
    (h : ∀ a b, f a = f b → g a = g b) :
    (Finset.univ.image g).card ≤ (Finset.univ.image f).card := by
  classical
  let φ : ℕ → ℕ := fun x => if hx : ∃ a, f a = x then g hx.choose else 0
  refine Finset.card_le_card_of_surjOn φ fun y hy => ?_
  rw [Finset.mem_coe, Finset.mem_image] at hy
  obtain ⟨a, -, rfl⟩ := hy
  have hx : ∃ b, f b = f a := ⟨a, rfl⟩
  refine ⟨f a, by simp, ?_⟩
  simp only [φ, dif_pos hx]
  exact h _ _ hx.choose_spec

theorem blocks_eq_of_imp {w w' : Equiv.Perm (Fin n)}
    (hinc : ∀ a b, β (w a) = β (w b) → δ a = δ b)
    (h' : ∀ a b, δ a = δ b ↔ β (w' a) = β (w' b)) :
    ∀ a b, δ a = δ b ↔ β (w a) = β (w b) := by
  classical
  have himage : ∀ v : Equiv.Perm (Fin n),
      Finset.univ.image (β ∘ v) = Finset.univ.image β := fun v => by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨a, ha⟩ => ⟨v a, ha⟩, fun ⟨a, ha⟩ => ⟨v⁻¹ a, by simpa using ha⟩⟩
  have hcard : (Finset.univ.image (β ∘ w)).card ≤ (Finset.univ.image δ).card := by
    rw [himage w, ← himage w']
    exact card_image_le_of_imp fun a b hab => (h' a b).1 hab

  let φ : ℕ → ℕ := fun x => if hx : ∃ a, β (w a) = x then δ hx.choose else 0
  have hφ : ∀ a, φ (β (w a)) = δ a := fun a => by
    have hx : ∃ b, β (w b) = β (w a) := ⟨a, rfl⟩
    simp only [φ, dif_pos hx]
    exact hinc _ _ hx.choose_spec
  have hmaps : Set.MapsTo φ (Finset.univ.image (β ∘ w) : Finset ℕ) (Finset.univ.image δ) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rw [Function.comp_apply, hφ]
    simp
  have hsurj : Set.SurjOn φ (Finset.univ.image (β ∘ w) : Finset ℕ) (Finset.univ.image δ) := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨a, -, rfl⟩ := hy
    exact ⟨β (w a), by simp, hφ a⟩
  have hinj := Finset.injOn_of_surjOn_of_card_le φ hmaps hsurj hcard
  intro a b
  refine ⟨fun hab => ?_, hinc a b⟩
  have ha : β (w a) ∈ (Finset.univ.image (β ∘ w) : Finset ℕ) := by simp
  have hb : β (w b) ∈ (Finset.univ.image (β ∘ w) : Finset ℕ) := by simp
  exact hinj ha hb (by rw [hφ, hφ, hab])

end Count

end Parabolic

end GroundTheory.Automorphic
