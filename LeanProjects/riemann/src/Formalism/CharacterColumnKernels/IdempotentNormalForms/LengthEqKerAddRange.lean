import Formalism.CharacterColumnKernels.StatementRho
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.RightMulEpsAlgebraMap

open Finset

noncomputable section

namespace Formalism.NG

namespace IdempotentNormalFormsRhoFacts

lemma length_eq_ker_add_range {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (φ : M →ₗ[R] P) :
    Module.length R M =
      Module.length R (LinearMap.ker φ) + Module.length R (LinearMap.range φ) :=
  Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    Subtype.val_injective φ.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))

lemma length_mono {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {A B : Submodule R M}
    (h : A ≤ B) : Module.length R A ≤ Module.length R B :=
  Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

lemma mem_annih {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw]
    [AddCommGroup Cs] [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P)
    (U : Submodule O Cs) (c : Cw) : c ∈ annih pr U ↔ ∀ x ∈ U, pr c x = 0 := by
  simp [annih, Submodule.mem_iInf, LinearMap.flip_apply]

lemma annih_anti {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw]
    [AddCommGroup Cs] [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P)
    {U V : Submodule O Cs} (h : U ≤ V) : annih pr V ≤ annih pr U := fun c hc =>
  (mem_annih pr U c).2 fun x hx => (mem_annih pr V c).1 hc x (h hx)

section Sel

variable {O C ι : Type*} [CommRing O] [AddCommGroup C] [Module O C]
  {Cw : ι → Type*} [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)]

lemma mem_sel (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (G : ∀ w, Submodule O (Cw w))
    (Q : Submodule O C) (x : C) :
    x ∈ Q ⊓ ⨅ w ∈ what₂, (G w).comap (res w) ↔ x ∈ Q ∧ ∀ w ∈ what₂, res w x ∈ G w := by
  simp [Submodule.mem_inf, Submodule.mem_iInf]

def relaxMap (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (F F' : ∀ w, Submodule O (Cw w))
    (Q : Submodule O C) :
    ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w)) →ₗ[O]
      ((w : what₂) → (F' w.1 ⧸ (F w.1).comap (F' w.1).subtype)) :=
  LinearMap.pi fun w => (Submodule.mkQ _) ∘ₗ
    ((res w.1 ∘ₗ Submodule.subtype _).codRestrict (F' w.1)
      fun x => ((mem_sel what₂ res F' Q x.1).mp x.2).2 w.1 w.2)

end Sel

end IdempotentNormalFormsRhoFacts

theorem lenChain : StatLenChain := by
  intro O H Zc C _ _ _ _ _ _ _ Ψ cl S hS
  let φ : LinearMap.range Ψ →ₗ[O] C := cl ∘ₗ (LinearMap.range Ψ).subtype
  have h1 := IdempotentNormalFormsRhoFacts.length_eq_ker_add_range Ψ
  have h2 := IdempotentNormalFormsRhoFacts.length_eq_ker_add_range φ
  have hk : Module.length O (LinearMap.ker φ) ≤
      Module.length O ↥(LinearMap.range Ψ ⊓ LinearMap.ker cl) := by
    refine Module.length_le_of_injective
      (((LinearMap.range Ψ).subtype ∘ₗ (LinearMap.ker φ).subtype).codRestrict _
        fun x => Submodule.mem_inf.mpr ⟨x.1.2, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp x.2)⟩)
      ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have hr : Module.length O (LinearMap.range φ) ≤ Module.length O S := by
    refine le_trans ?_ (IdempotentNormalFormsRhoFacts.length_mono (A := LinearMap.range φ) ?_)
    · exact le_rfl
    · rintro _ ⟨⟨z, hz⟩, rfl⟩
      obtain ⟨h, rfl⟩ := LinearMap.mem_range.mp hz
      exact hS ⟨h, rfl⟩
  rw [h1, h2, add_assoc]
  gcongr

namespace IdempotentNormalFormsRhoFacts

section Sel2

variable {O C ι : Type*} [CommRing O] [AddCommGroup C] [Module O C]
  {Cw : ι → Type*} [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)]
  (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (F F' : ∀ w, Submodule O (Cw w)) (Q : Submodule O C)

lemma relaxMap_apply (x : ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w))) (w : what₂) :
    relaxMap what₂ res F F' Q x w =
      Submodule.Quotient.mk ⟨res w.1 x.1, ((mem_sel what₂ res F' Q x.1).mp x.2).2 w.1 w.2⟩ :=
  rfl

lemma mem_of_relaxMap (x : ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w)))
    (hx : relaxMap what₂ res F F' Q x = 0) : x.1 ∈ Q ⊓ ⨅ w ∈ what₂, (F w).comap (res w) := by
  refine (mem_sel what₂ res F Q x.1).mpr ⟨((mem_sel what₂ res F' Q x.1).mp x.2).1, fun w hw => ?_⟩
  have h0 := congrFun hx ⟨w, hw⟩
  rw [relaxMap_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
  exact h0

lemma length_ker_relaxMap_le :
    Module.length O (LinearMap.ker (relaxMap what₂ res F F' Q)) ≤
      Module.length O ↥(Q ⊓ ⨅ w ∈ what₂, (F w).comap (res w)) := by
  rw [(Submodule.equivMapOfInjective _ (Submodule.injective_subtype _)
    (LinearMap.ker (relaxMap what₂ res F F' Q))).length_eq]
  apply length_mono
  rintro _ ⟨x, hx, rfl⟩
  exact mem_of_relaxMap what₂ res F F' Q x (LinearMap.mem_ker.mp hx)

lemma length_pi_rows :
    Module.length O ((w : what₂) → (F' w.1 ⧸ (F w.1).comap (F' w.1).subtype)) =
      ∑ w ∈ what₂, Module.length O (F' w ⧸ (F w).comap (F' w).subtype) := by
  rw [Module.length_pi_of_fintype (R := O)
    (fun w : what₂ => (F' w.1 ⧸ (F w.1).comap (F' w.1).subtype))]
  exact Finset.sum_coe_sort what₂ (fun w => Module.length O (F' w ⧸ (F w).comap (F' w).subtype))

end Sel2

end IdempotentNormalFormsRhoFacts

theorem selRelax : StatSelRelax := by
  intro O C ι _ _ _ what₂ Cw _ _ res F F' Q _
  rw [IdempotentNormalFormsRhoFacts.length_eq_ker_add_range (IdempotentNormalFormsRhoFacts.relaxMap what₂ res F F' Q), ← IdempotentNormalFormsRhoFacts.length_pi_rows]
  gcongr
  · exact IdempotentNormalFormsRhoFacts.length_ker_relaxMap_le what₂ res F F' Q
  · exact Module.length_le_of_injective (Submodule.subtype _) Subtype.val_injective

theorem annColength : StatAnnColength := by
  intro O Cw Cs _ _ _ _ _ _ _ pr Fs Im hle
  let I' : Submodule O Fs := Im.comap Fs.subtype
  let Φ : annih pr Im →ₗ[O] ((Fs ⧸ I') →ₗ[O] KO O) :=
    { toFun := fun c => I'.liftQ (pr c.1 ∘ₗ Fs.subtype) (fun x hx => by
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
        exact (IdempotentNormalFormsRhoFacts.mem_annih pr Im c.1).1 c.2 x.1 hx)
      map_add' := fun a b => by ext x; simp
      map_smul' := fun r a => by ext x; simp }
  have hker : LinearMap.ker Φ ≤ (annih pr Fs).comap (annih pr Im).subtype := by
    intro c hc
    rw [Submodule.mem_comap, Submodule.subtype_apply, IdempotentNormalFormsRhoFacts.mem_annih]
    intro x hx
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hc) (Submodule.Quotient.mk ⟨x, hx⟩)
    simpa [Φ] using this
  have hle' : (annih pr Fs).comap (annih pr Im).subtype ≤ LinearMap.ker Φ := by
    intro c hc
    rw [Submodule.mem_comap, Submodule.subtype_apply, IdempotentNormalFormsRhoFacts.mem_annih] at hc
    rw [LinearMap.mem_ker]
    ext x
    simp [Φ, hc x.1 x.2]
  have hinj := LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ Φ hle' hker)
  by_cases hfinQ : IsFiniteLength O (Fs ⧸ I')
  swap
  · rw [← Module.length_ne_top_iff, ne_eq, not_not] at hfinQ
    exact hfinQ ▸ le_top
  calc _ ≤ Module.length O ((Fs ⧸ I') →ₗ[O] KO O) := Module.length_le_of_injective _ hinj
    _ = _ := matlis O (Fs ⧸ I') hfinQ

theorem torsLen : StatTorsLen := by
  classical
  intro O _ _ _ d _ δ
  have hmap : DistribSMul.toLinearMap O (d → KO O) (δ * δ) =
      matQ O (Matrix.diagonal fun _ : d => δ * δ) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [matQ, relMap, Matrix.diagonal_apply, ite_smul]
  rw [hmap, lenKer, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    AddValuation.map_pow, AddValuation.map_mul, two_mul, nsmul_eq_mul]

namespace IdempotentNormalFormsRhoFacts

lemma mid_bound {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type*}
    [Group G] {d : Type} [Fintype d] (ρM : Representation O G (d → KO O)) {H : Type*}
    [AddCommGroup H] [Module O H] (Ψ : H →ₗ[O] coZ1s ρM) (δ : O)
    (hcob : ∀ h : H, ∀ v : d → KO O, (Ψ h : G → (d → KO O)) = coD0 ρM v → (δ * δ) • v = 0) :
    Module.length O ↥(LinearMap.range Ψ ⊓
        LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ) ≤
      (Fintype.card d : ℕ∞) * (2 * IsDiscreteValuationRing.addVal O δ) := by
  set T := LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) (δ * δ))
  have hle : ∀ z : ↥(LinearMap.range Ψ ⊓
      LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ),
      (z.1 : G → (d → KO O)) ∈ T.map (coD0 ρM) := by
    rintro ⟨z, hz⟩
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
    obtain ⟨h, rfl⟩ := LinearMap.mem_range.mp hz1
    have h3 : Ψ h ∈ (coB1 ρM).comap (coZ1s ρM).subtype := by
      rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz2
      exact hz2
    rw [Submodule.mem_comap, Submodule.subtype_apply, coB1, LinearMap.mem_range] at h3
    obtain ⟨v, hv⟩ := h3
    refine Submodule.mem_map.mpr ⟨v, LinearMap.mem_ker.mpr ?_, hv⟩
    simpa using hcob h v hv.symm
  calc _ ≤ Module.length O ↥(T.map (coD0 ρM)) := by
        refine Module.length_le_of_injective
          (((coZ1s ρM).subtype ∘ₗ Submodule.subtype _).codRestrict _ hle) ?_
        intro x y hxy
        have := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext this)
    _ ≤ Module.length O T :=
        Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)
    _ = _ := torsLen O d δ

lemma final_arith (R X Y Z s k : ℕ∞) (c N vδ : ℕ∞) (hk : k ≤ X + c * N * vδ)
    (hm : Y ≤ N * (2 * vδ)) (hs : Z ≤ s + R) :
    k + Y + Z ≤ R + X + s + 4 * N * (c + 1) * vδ := by
  calc k + Y + Z ≤ (X + c * N * vδ) + N * (2 * vδ) + (s + R) := add_le_add (add_le_add hk hm) hs
    _ ≤ (X + c * N * vδ) + N * (2 * vδ) + (s + R) + (3 * c * N * vδ + 2 * N * vδ) := le_self_add
    _ = R + X + s + 4 * N * (c + 1) * vδ := by ring

end IdempotentNormalFormsRhoFacts

end Formalism.NG
