import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicFiniteOpenDecompositionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ColumnSep

theorem exists_sub_evals_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [DecidableEq β]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    {c : β → α → Type} [∀ j i, Fintype (c j i)] [∀ j i, DecidableEq (c j i)]
    (g : ∀ j, (Σ i, c j i) ≃ m' j) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (∀ j, GlobalTheory.SmGL.Levi k (c j)) W) (ψ : (∀ j, GlobalTheory.SmGL.Levi k (c j)) →* ℂˣ),
    (∀ z w, τ z w = (ψ z : ℂ) • w) → ∀ (j₀ : β) (ν : GlobalTheory.SmGL.Levi k m' →* ℂˣ)
    (s : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind (GlobalTheory.SmGL.relParab k g)
      ((GlobalTheory.SmGL.twist τ (GlobalTheory.SmGL.relDeltaHalf k c)).comp (GlobalTheory.SmGL.relProj k g)))),
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → ∀ j, GL (m' j) k) (l : ι → Module.Dual ℂ W)
      (R : Subrepresentation ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.relInd g τ) ν).comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀))),
      s ∈ R.toSubmodule ∧ ∀ F ∈ R.toSubmodule,
        (∀ i x, l i (F.1.1 (Function.update (y i) j₀ x)) = 0) → F = 0 := by
  intro k _ _ _ _ α β _ _ _ _ _ m' _ _ c _ _ g W _ _ τ ψ hτ j₀ ν s
  classical

  have hlaw : ∀ (F : indSpace (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g)))
      (p : Levi k m'), p ∈ relParab k g → ∀ x, ∃ a : ℂ, F.1 (p * x) = a • F.1 x := by
    intro F p hp x
    refine ⟨((relDeltaHalf k c (relProj k g ⟨p, hp⟩) : ℂˣ) : ℂ) * (ψ (relProj k g ⟨p, hp⟩) : ℂ), ?_⟩
    rw [show p * x = ((⟨p, hp⟩ : relParab k g) : Levi k m') * x from rfl, F.2 ⟨p, hp⟩ x]
    simp [twist_apply, hτ, smul_smul]
  have hP : ∀ p : Levi k m', (∀ j, p j ∈ parab k (g j)) → p ∈ relParab k g := fun p h j _ => h j

  let St : Subgroup (Levi k m') :=
    { carrier := {x | ∀ y, s.1.1 (y * x) = s.1.1 y}
      mul_mem' := fun {a b} ha hb y => by rw [← mul_assoc, hb, ha]
      one_mem' := fun y => by rw [mul_one]
      inv_mem' := fun {a} ha y => by rw [← ha (y * a⁻¹), inv_mul_cancel_right] }
  have hSt : IsOpen (St : Set (Levi k m')) := by
    have h2 : IsOpen {x : Levi k m' | ind (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g)) x s.1 = s.1} := s.2
    convert h2 using 1
    ext x
    exact ⟨fun h => Subtype.ext (funext h), fun h y => congrFun (congrArg Subtype.val h) y⟩
  let K : ∀ j, Subgroup (GL (m' j) k) := fun j => St.comap (MonoidHom.mulSingle (fun j => GL (m' j) k) j)
  have hK : ∀ j, IsOpen (K j : Set (GL (m' j) k)) := fun j => hSt.preimage (continuous_mulSingle j)
  have hpi : Subgroup.pi Set.univ K ≤ St := Subgroup.pi_le_iff.2 fun j => Subgroup.map_comap_le _ _
  have hpiK : ∀ κ : Levi k m', (∀ j, κ j ∈ K j) → ∀ y, s.1.1 (y * κ) = s.1.1 y :=
    fun κ h => hpi (fun j _ => h j)

  choose Y hY using fun j => GlobalTheory.T.parabolic_finite_open_decomposition k (g j) (K j) (hK j)
  have hdec : ∀ z : Levi k m', ∃ p : Levi k m', (∀ j, p j ∈ parab k (g j)) ∧ ∃ y : Levi k m',
      y ∈ Fintype.piFinset Y ∧ ∃ κ : Levi k m', (∀ j, κ j ∈ K j) ∧ z = p * y * κ := by
    intro z
    choose p hp y hy κ hκ e using fun j => hY j (z j)
    exact ⟨p, hp, y, Fintype.mem_piFinset.2 hy, κ, hκ, funext e⟩

  let W₀ : Submodule ℂ W := Submodule.span ℂ (Set.range fun y : Fintype.piFinset Y => s.1.1 y)
  haveI : FiniteDimensional ℂ W₀ := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hsW : ∀ x, s.1.1 x ∈ W₀ := by
    intro x
    obtain ⟨p, hp, y, hy, κ, hκ, rfl⟩ := hdec x
    obtain ⟨a, ha⟩ := hlaw s.1 p (hP p hp) (y * κ)
    rw [mul_assoc, ha, hpiK κ hκ y]
    exact W₀.smul_mem a (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)

  let ρ' := (twist (relInd g τ) ν).comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀)
  have hact : ∀ h F x, (ρ' h F).1.1 x =
      (ν (Pi.mulSingle j₀ h) : ℂ) • F.1.1 (x * Pi.mulSingle j₀ h) := fun h F x => rfl
  have hcomm : ∀ (κ : Levi k m'), κ j₀ = 1 → ∀ h : GL (m' j₀) k,
      κ * Pi.mulSingle j₀ h = Pi.mulSingle j₀ h * κ := by
    intro κ hκ h
    funext j
    by_cases hj : j = j₀
    · subst hj; simp [hκ]
    · simp [Pi.mulSingle_apply, hj]
  let R : Subrepresentation ρ' :=
    { toSubmodule :=
        { carrier := {F | (∀ κ : Levi k m', κ j₀ = 1 → (∀ j, κ j ∈ K j) → ∀ x, F.1.1 (x * κ) = F.1.1 x) ∧
            ∀ x, F.1.1 x ∈ W₀}
          add_mem' := by
            rintro F G ⟨hF1, hF2⟩ ⟨hG1, hG2⟩
            refine ⟨fun κ h1 h2 x => ?_, fun x => ?_⟩
            · show F.1.1 (x * κ) + G.1.1 (x * κ) = F.1.1 x + G.1.1 x
              rw [hF1 κ h1 h2, hG1 κ h1 h2]
            · exact W₀.add_mem (hF2 x) (hG2 x)
          zero_mem' := ⟨fun κ _ _ x => rfl, fun x => W₀.zero_mem⟩
          smul_mem' := by
            rintro a F ⟨hF1, hF2⟩
            refine ⟨fun κ h1 h2 x => ?_, fun x => ?_⟩
            · show a • F.1.1 (x * κ) = a • F.1.1 x
              rw [hF1 κ h1 h2]
            · exact W₀.smul_mem a (hF2 x) }
      apply_mem_toSubmodule := by
        rintro h F ⟨hF1, hF2⟩
        refine ⟨fun κ h1 h2 x => ?_, fun x => ?_⟩
        · rw [hact, hact, mul_assoc, hcomm κ h1 h, ← mul_assoc, hF1 κ h1 h2]
        · rw [hact]
          exact W₀.smul_mem _ (hF2 _) }
  have hsR : s ∈ R.toSubmodule := ⟨fun κ _ h2 x => hpiK κ h2 x, hsW⟩

  let b := Module.finBasis ℂ W₀
  choose L hL using fun t : Fin (Module.finrank ℂ W₀) => LinearMap.exists_extend (b.coord t)
  refine ⟨Fintype.piFinset Y × Fin (Module.finrank ℂ W₀), inferInstance, fun i => i.1.1, fun i => L i.2, R,
    hsR, ?_⟩
  rintro F ⟨hF1, hF2⟩ hF0
  have hz : ∀ y ∈ Fintype.piFinset Y, ∀ x, F.1.1 (Function.update y j₀ x) = 0 := by
    intro y hy x
    have hw := hF2 (Function.update y j₀ x)
    have hc : ∀ t, b.coord t ⟨_, hw⟩ = 0 := by
      intro t
      rw [← hL t]
      exact hF0 (⟨y, hy⟩, t) x
    exact congrArg Subtype.val (b.forall_coord_eq_zero_iff.1 hc)
  refine Subtype.ext (Subtype.ext (funext fun z => ?_))
  show F.1.1 z = 0
  obtain ⟨p, hp, y, hy, κ, hκ, e⟩ := hdec z
  have hp' : ∀ j, Function.update p j₀ 1 j ∈ parab k (g j) := by
    intro j
    by_cases hj : j = j₀
    · subst hj; simp [one_mem]
    · simp [hj, hp j]
  have hκ' : ∀ j, Function.update κ j₀ 1 j ∈ K j := by
    intro j
    by_cases hj : j = j₀
    · subst hj; simp [one_mem]
    · simp [hj, hκ j]
  have hz' : z = Function.update p j₀ 1 * (Function.update y j₀ (z j₀) * Function.update κ j₀ 1) := by
    funext j
    by_cases hj : j = j₀
    · subst hj; simp
    · simp [hj, e, mul_assoc]
  obtain ⟨a, ha⟩ := hlaw F.1 _ (hP _ hp') (Function.update y j₀ (z j₀) * Function.update κ j₀ 1)
  rw [hz', ha, hF1 _ (by simp) hκ', hz y hy, smul_zero]

end GlobalTheory.ColumnSep
