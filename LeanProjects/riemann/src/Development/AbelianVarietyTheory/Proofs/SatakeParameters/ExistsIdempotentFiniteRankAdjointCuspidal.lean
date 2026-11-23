import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BarKHomSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfiniteStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemisimpleOfLocallyFiniteCompactGroupStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplementWithoutCommonIrreducibleTypesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOrthogonalOfNoCommonIrreducibleTypesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTypeClosurePreservedByArchCompactIntertwStatement

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.PRep GlobalTheory.Published

namespace GlobalTheory.IdemAdj

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem coeffSpan_mul_right {W : Type} [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W)
    (k' : Kinf E a) {f : Kinf E a → ℂ} (hf : f ∈ AutFin.coeffSpan ρ₀) : (fun k => f (k * k')) ∈ AutFin.coeffSpan ρ₀ := by
  let T : (Kinf E a → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    { toFun := fun f k => f (k * k'), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have : AutFin.coeffSpan ρ₀ ≤ (AutFin.coeffSpan ρ₀).comap T := Submodule.span_le.2 (by
    rintro _ ⟨ℓ, w, rfl⟩
    exact Submodule.subset_span ⟨ℓ, ρ₀ k' w, funext fun k => by simp [T, map_mul]⟩)
  exact this hf

def typeSub (π : CuspSub E a) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) :
    Subrepresentation (cptOn π) where
  toSubmodule :=
    { carrier := {ψ | ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ₀}
      add_mem' := fun {x y} hx hy g => by
        have e : (fun k : Kinf E a => (cptRep E a k (x + y).1).1 g) =
            (fun k : Kinf E a => (cptRep E a k x.1).1 g) + (fun k : Kinf E a => (cptRep E a k y.1).1 g) := by
          funext k; simp
        rw [e]; exact add_mem (hx g) (hy g)
      zero_mem' := fun g => by
        have e : (fun k : Kinf E a => (cptRep E a k (0 : π.V).1).1 g) = 0 := by funext k; simp
        rw [e]; exact zero_mem _
      smul_mem' := fun c x hx g => by
        have e : (fun k : Kinf E a => (cptRep E a k (c • x).1).1 g) = c • (fun k : Kinf E a => (cptRep E a k x.1).1 g) := by
          funext k; simp
        rw [e]; exact Submodule.smul_mem _ c (hx g) }
  apply_mem_toSubmodule k' ψ hψ g := by
    have e : (fun k : Kinf E a => (cptRep E a k (cptOn π k' ψ).1).1 g) =
        fun k => (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) (k * k') := by
      funext k; simp [map_mul, act]
    rw [e]; exact coeffSpan_mul_right ρ₀ k' (hψ g)

theorem adj_of_isCompl {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) {X Y : Submodule ℂ V} {X' Y' : Submodule ℂ V'} (h : IsCompl X Y) (h' : IsCompl X' Y')
    (h1 : ∀ y ∈ Y, ∀ x' ∈ X', B y x' = 0) (h2 : ∀ x ∈ X, ∀ y' ∈ Y', B x y' = 0) (φ : V) (ψ : V') :
    B (X.projection Y h φ) ψ = B φ (X'.projection Y' h' ψ) := by
  have eφ := Submodule.projection_add_projection_eq_self h φ
  have eψ := Submodule.projection_add_projection_eq_self h' ψ
  have m1 := h2 _ (Submodule.projection_apply_mem h φ) _ (Submodule.projection_apply_mem h'.symm ψ)
  have m2 := h1 _ (Submodule.projection_apply_mem h.symm φ) _ (Submodule.projection_apply_mem h' ψ)
  calc B (X.projection Y h φ) ψ = B (X.projection Y h φ) (X'.projection Y' h' ψ + Y'.projection X' h'.symm ψ) := by
        rw [eψ]
    _ = B (X.projection Y h φ + Y.projection X h.symm φ) (X'.projection Y' h' ψ) := by
        rw [map_add, map_add, LinearMap.add_apply, m1, m2]
    _ = _ := by rw [eφ]

theorem idem_adj {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (σ : G →* G) {H : Subgroup G} (hH : IsCompact (H : Set G))
    (hH' : IsCompact ((H.map σ : Subgroup G) : Set G)) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) (φ ψ : V) :
    B (LocGL.idem hρ hH φ) ψ = B φ (LocGL.idem hρ hH' ψ) := by
  refine adj_of_isCompl B (LocGL.isCompl_fixed_twKer hρ hH) (LocGL.isCompl_fixed_twKer hρ hH') ?_ ?_ φ ψ
  · intro y hy x' hx'
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, v, rfl⟩ := hz
      have hf : ρ (σ n) x' = x' := GlobalTheory.Parabolic.mem_fixed.1 hx' _ ⟨n, n.2, rfl⟩
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, LinearMap.sub_apply]
      rw [← hB n v x', hf, sub_self]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  · intro x hx y' hy'
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨m, hm⟩, w, rfl⟩ := hz
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hm
      have hf : ρ n x = x := GlobalTheory.Parabolic.mem_fixed.1 hx _ hn
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
      rw [← hB n x w, hf, sub_self]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]

theorem finiteDimensional_typeSub_fixed (h : AutomorphicFormsFiniteGL) (π : CuspSub E a) {W : Type} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] {ρ₀ : Representation ℂ (Kinf E a) W} (hρ₀ : AutFin.IsContRep ρ₀)
    {K' : Subgroup (GL (Fin a) (Af E))} (hK : IsOpen (K' : Set (GL (Fin a) (Af E)))) :
    FiniteDimensional ℂ ↥((typeSub π ρ₀).toSubmodule ⊓ fixed π.finPart K') := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ π.V, cap τ u φ = c • φ := fun τ u =>
    π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a K' hK W ρ₀ hρ₀ c
  refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ ((typeSub π ρ₀).toSubmodule ⊓ fixed π.finPart K').subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms K' ρ₀ c))
    fun v => Submodule.subset_span ⟨(π.cusp _ v.1.2).1, fun k hk => congrArg Subtype.val
      (GlobalTheory.Parabolic.mem_fixed.1 v.2.2 k hk), v.2.1, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))

theorem exists_idem_adj : AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ)
    (π : CuspSub L a), ∃ P : Module.End ℂ π.V, P ≠ 0 ∧ P ∘ₗ P = P ∧ FiniteDimensional ℂ (LinearMap.range P) ∧
      ∀ s : Op L a → Op L a, (s = invTOp ∨ s = conjOp) → ∀ B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ,
        (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) →
        (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (s (.fin k)) ψ) = B φ ψ) →
        (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (s (.cpt k)) ψ) = B φ ψ) →
        (∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (s (.lie X)) ψ) = 0) →
        ∃ P' : Module.End ℂ π.V, ∀ φ ψ, B (P φ) ψ = B φ (P' ψ) := by
  intro h L _ _ _ a π
  haveI := GlobalTheory.T.compactSpace_maximalCompact_unitary_infinite L a

  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ₀ : π.V := ⟨φ, hφ⟩ with hφ₀
  have h0' : φ₀ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact L a
  set K' : Subgroup (GL (Fin a) (Af L)) := U ⊓ LocEx.stab π.finPart φ₀ with hK'
  have hKo : IsOpen (K' : Set (GL (Fin a) (Af L))) := hUo.inter (π.isSmooth_finPart φ₀)
  have hKc : IsCompact (K' : Set (GL (Fin a) (Af L))) :=
    hUc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_left

  set O := LocEx.orbSpan φ with hO
  haveI : FiniteDimensional ℂ O := (π.cusp φ hφ).1.kfin
  set ρ₀ := sub (cptRep L a) O (LocEx.orbSpan_stable φ) with hρ₀
  have hρc : AutFin.IsContRep ρ₀ := LocEx.isContRep_sub _ _

  have hloc : ∀ v : π.V, ∃ U : Submodule ℂ π.V, v ∈ U ∧ FiniteDimensional ℂ U ∧
      (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ π.V), ∀ u ∈ U, Continuous fun k => ℓ (cptOn π k u) := by
    intro v
    have hSV : LocEx.orbSpan v.1 ≤ π.V := Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact (π.op (.cpt k) v).2)
    haveI : FiniteDimensional ℂ (LocEx.orbSpan v.1) := (π.cusp v.1 v.2).1.kfin
    set Uv : Submodule ℂ π.V := (LocEx.orbSpan v.1).comap π.V.subtype
    refine ⟨Uv, Submodule.subset_span ⟨1, by simp⟩, ?_, fun k u hu => ?_, fun ℓ u hu => ?_⟩
    · exact FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Uv.subtype).codRestrict (LocEx.orbSpan v.1)
        fun u => u.2) fun u u' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    · exact LocEx.orbSpan_stable v.1 k u.1 hu
    · have := LocEx.isContRep_sub (LocEx.orbSpan v.1) (LocEx.orbSpan_stable v.1)
        (ℓ ∘ₗ Submodule.inclusion hSV) ⟨u.1, hu⟩
      convert this using 2 with k
      rfl
  obtain ⟨hss, hfin, hsum⟩ := GlobalTheory.T.isSemisimple_of_locallyFinite_compactGroup (Kinf L a) π.V (cptOn π) hloc

  set X := typeSub π ρ₀ with hX
  have hφX : φ₀ ∈ X.toSubmodule := fun g =>
    AutFinGL.type_of_map ρ₀ O.subtype (fun _ _ => rfl) ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩ g
  have hclos : ∀ S₁ S₂ : Subrepresentation (cptOn π), IsAtom S₁ → S₂ ≤ X →
      Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X := by
    rintro S₁ S₂ hS₁ hS₂ ⟨e⟩
    haveI := hfin S₁ hS₁
    haveI : FiniteDimensional ℂ S₂.toSubmodule := LinearEquiv.finiteDimensional e.toLinearEquiv
    obtain ⟨F, hF⟩ := LinearMap.exists_extend (S₁.toSubmodule.subtype ∘ₗ e.symm.toLinearEquiv.toLinearMap)
    have hFv : ∀ u (hu : u ∈ S₂.toSubmodule), F u = (e.symm ⟨u, hu⟩ : π.V) := fun u hu =>
      LinearMap.congr_fun hF ⟨u, hu⟩
    intro x hx
    have hx' : x = F (e ⟨x, hx⟩) := by
      rw [hFv _ (e ⟨x, hx⟩).2]
      simp
    rw [hx']
    refine GlobalTheory.T.cuspidal_typeClosure_preserved_by_archCompact_intertwiner L a π O ρ₀ S₂.toSubmodule inferInstance (fun k u hu => S₂.apply_mem_toSubmodule k hu) F
      (fun k u hu => ?_) _ (e ⟨x, hx⟩).2 (hS₂ (e ⟨x, hx⟩).2)
    rw [hFv _ (S₂.apply_mem_toSubmodule k hu), hFv _ hu]
    have := e.symm.toIntertwiningMap.isIntertwining' k
    exact congrArg Subtype.val (LinearMap.congr_fun this ⟨u, hu⟩)
  obtain ⟨Y, hXY, hnoiso, hT⟩ := GlobalTheory.T.exists_complement_without_common_irreducible_types (Kinf L a) π.V (cptOn π) hss hsum X hclos

  set e := LocGL.idem π.isSmooth_finPart hKc with he
  have hcomm : ∀ g k (v : π.V), π.finPart g (cptOn π k v) = cptOn π k (π.finPart g v) := fun g k v => by
    refine Subtype.ext ?_
    change (rt L a (finGL L a g) * rt L a (infGL L a (Unitary.toUnits k))) v.1 =
      (rt L a (infGL L a (Unitary.toUnits k)) * rt L a (finGL L a g)) v.1
    rw [← map_mul, ← map_mul, infGL_comm]
  have hfixS : ∀ k, ∀ v ∈ fixed π.finPart K', cptOn π k v ∈ fixed π.finPart K' := fun k v hv =>
    GlobalTheory.Parabolic.mem_fixed.2 fun u hu => by rw [hcomm, GlobalTheory.Parabolic.mem_fixed.1 hv u hu]
  have hkerS : ∀ k, ∀ v ∈ twKer π.finPart K' 1, cptOn π k v ∈ twKer π.finPart K' 1 := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, w, rfl⟩ := hz
      exact Submodule.subset_span ⟨n, cptOn π k w, by rw [map_sub, map_smul, hcomm]⟩
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu
  have hee : ∀ v, e (e v) = e v := fun v => LocGL.idem_of_mem _ _ (LocGL.idem_mem _ _ v)
  have heq : ∀ k v, e (cptOn π k v) = cptOn π k (e v) := by
    intro k v
    have hd : v - e v ∈ twKer π.finPart K' 1 := by
      rw [← LocGL.idem_eq_zero_iff π.isSmooth_finPart hKc, map_sub, hee, sub_self]
    have hv : v = e v + (v - e v) := by abel
    conv_lhs => rw [hv, map_add, map_add]
    rw [LocGL.idem_of_mem _ _ (hfixS k _ (LocGL.idem_mem _ _ v)),
      (LocGL.idem_eq_zero_iff π.isSmooth_finPart hKc).2 (hkerS k _ hd), add_zero]
  obtain ⟨heX, heY⟩ := hT e heq

  set PT := X.toSubmodule.projection Y.toSubmodule hXY with hPT
  have hPTl : ∀ v ∈ X.toSubmodule, PT v = v := fun v hv => by
    rw [hPT]; exact Submodule.projection_apply_of_mem_left hXY hv
  have hPTr : ∀ v ∈ Y.toSubmodule, PT v = 0 := fun v hv => by
    rw [hPT]; exact Submodule.projection_apply_of_mem_right hXY hv
  have hPTm : ∀ v, PT v ∈ X.toSubmodule := fun v => by
    rw [hPT]; exact Submodule.projection_apply_mem hXY v
  have hPTs : ∀ v, PT v + Y.toSubmodule.projection X.toSubmodule hXY.symm v = v := fun v => by
    rw [hPT]; exact Submodule.projection_add_projection_eq_self hXY v
  have hPTe : ∀ v, PT (e v) = e (PT v) := by
    intro v
    have hv := hPTs v
    conv_lhs => rw [← hv, map_add, map_add]
    rw [hPTl _ (heX _ (hPTm v)), hPTr _ (heY _ (Submodule.projection_apply_mem hXY.symm v)), add_zero]
  have hPT2 : ∀ v, PT (PT v) = PT v := fun v => hPTl _ (hPTm v)
  refine ⟨e ∘ₗ PT, ?_, ?_, ?_, ?_⟩
  · intro hP
    have h1 : (e ∘ₗ PT) φ₀ = φ₀ := by
      change e (PT φ₀) = φ₀
      rw [hPTl _ hφX]
      exact LocGL.idem_of_mem _ _ (GlobalTheory.Parabolic.mem_fixed.2 fun u hu => hu.2)
    rw [hP] at h1
    exact h0' h1.symm
  · refine LinearMap.ext fun v => ?_
    change e (PT (e (PT v))) = e (PT v)
    rw [hPTe, hee, hPT2]
  · have hle : LinearMap.range (e ∘ₗ PT) ≤ X.toSubmodule ⊓ fixed π.finPart K' := by
      rintro _ ⟨v, rfl⟩
      exact ⟨heX _ (hPTm v), LocGL.idem_mem π.isSmooth_finPart hKc _⟩
    haveI := finiteDimensional_typeSub_fixed h π hρc hKo (ρ₀ := ρ₀)
    exact Submodule.finiteDimensional_of_le hle
  · intro s hs B hl hr hfinB hcptB _
    obtain ⟨σ, hσc, hσ⟩ : ∃ σ : GL (Fin a) (Af L) →* GL (Fin a) (Af L), Continuous σ ∧
        ∀ k, s (.fin k) = .fin (σ k) := by
      rcases hs with rfl | rfl
      · refine ⟨invT a (Af L), ?_, fun k => rfl⟩
        refine Units.continuous_iff.2 ⟨?_, ?_⟩
        · exact (Units.continuous_val.comp continuous_inv).matrix_transpose
        · exact Units.continuous_val.matrix_transpose
      · exact ⟨Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv),
          Continuous.units_map _ (continuous_id.matrix_map (continuous_conjFin _)), fun k => rfl⟩
    have hsK : ∀ k, s (.cpt k) = .cpt (barKHom L a k) := by
      rcases hs with rfl | rfl <;> exact fun k => rfl
    have hBf : ∀ k φ ψ, B (π.finPart k φ) (π.finPart (σ k) ψ) = B φ ψ := fun k φ ψ => by
      have := hfinB k φ ψ
      rw [hσ] at this
      exact this
    have hBc : ∀ k φ ψ, B (cptOn π k φ) (cptOn π (barKHom L a k) ψ) = B φ ψ := fun k φ ψ => by
      have := hcptB k φ ψ
      rw [hsK] at this
      exact this
    have hKc' : IsCompact ((K'.map σ : Subgroup _) : Set (GL (Fin a) (Af L))) := by
      rw [Subgroup.coe_map]; exact hKc.image hσc
    have hC := GlobalTheory.T.isCompl_orthogonal_of_no_common_irreducible_types (Kinf L a) π.V (cptOn π) (barKHom L a) barKHom_surjective hfin hsum B hl hr hBc X Y hXY hnoiso
    refine ⟨(Submodule.projection _ _ hC) ∘ₗ LocGL.idem π.isSmooth_finPart hKc', fun φ ψ => ?_⟩
    change B (e (PT φ)) ψ = B φ (Submodule.projection _ _ hC (LocGL.idem π.isSmooth_finPart hKc' ψ))
    rw [idem_adj π.isSmooth_finPart σ hKc hKc' B hBf]
    rw [hPT]
    refine adj_of_isCompl B hXY hC (fun y hy x' hx' => ?_) (fun x hx y' hy' => ?_) φ _
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx'
      exact hx' y hy
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hy'
      exact hy' x hx

end GlobalTheory.IdemAdj

end
