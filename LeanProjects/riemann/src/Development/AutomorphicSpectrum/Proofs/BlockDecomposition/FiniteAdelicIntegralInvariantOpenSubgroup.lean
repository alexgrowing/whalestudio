import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

def HasCO (G : Type) [AddGroup G] [TopologicalSpace G] : Prop :=
  ∀ W ∈ 𝓝 (0 : G), ∃ P : AddSubgroup G, IsOpen (P : Set G) ∧ IsCompact (P : Set G) ∧ (P : Set G) ⊆ W

theorem HasCO.pi {ι : Type} [Finite ι] {G : ι → Type} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)] (h : ∀ i, HasCO (G i)) : HasCO (∀ i, G i) := by
  intro W hW
  rw [nhds_pi] at hW
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.1 hW
  choose P hPo hPc hPW using fun i => h i (t i) (ht i)
  have hcoe : ((AddSubgroup.pi Set.univ P : AddSubgroup (∀ i, G i)) : Set (∀ i, G i)) =
      Set.univ.pi fun i => (P i : Set (G i)) := by
    ext x
    simp [AddSubgroup.mem_pi]
  refine ⟨AddSubgroup.pi Set.univ P, ?_, ?_, ?_⟩
  · rw [hcoe]
    exact isOpen_set_pi Set.finite_univ fun i _ => hPo i
  · rw [hcoe]
    exact isCompact_univ_pi hPc
  · intro x hx
    rw [hcoe] at hx
    exact hsub fun i _ => hPW i (hx i (Set.mem_univ i))

theorem HasCO.comap {G H : Type} [AddGroup G] [TopologicalSpace G] [AddGroup H] [TopologicalSpace H]
    (h : HasCO H) (f : G →+ H) (hf : IsHomeomorph f) : HasCO G := by
  intro W hW
  let e : G ≃ₜ H := hf.homeomorph f
  have he : ∀ x, e x = f x := fun _ => rfl
  have h0 : e.symm 0 = 0 := by
    apply e.injective
    rw [e.apply_symm_apply, he, map_zero]
  have hW' : e.symm ⁻¹' W ∈ 𝓝 (0 : H) := by
    apply e.symm.continuous.continuousAt.preimage_mem_nhds
    rwa [h0]
  obtain ⟨P, hPo, hPc, hPW⟩ := h _ hW'
  refine ⟨P.comap f, hPo.preimage hf.continuous, ?_, ?_⟩
  · have : ((P.comap f : AddSubgroup G) : Set G) = e.symm '' (P : Set H) := by
      ext x
      constructor
      · intro hx
        exact ⟨e x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        change f (e.symm y) ∈ P
        rw [← he]
        simpa using hy
    rw [this]
    exact hPc.image e.symm.continuous
  · intro x hx
    have h1 : e.symm (e x) ∈ W := hPW (by rw [he]; exact hx)
    rwa [e.symm_apply_apply] at h1

theorem HasCO.sub {G : Type} [AddGroup G] [TopologicalSpace G] (h : HasCO G) (S : AddSubgroup G)
    (hS : IsClosed (S : Set G)) : HasCO S := by
  intro W hW
  obtain ⟨W', hW', hsub⟩ := mem_nhds_subtype (S : Set G) 0 W |>.1 hW
  obtain ⟨P, hPo, hPc, hPW⟩ := h W' hW'
  refine ⟨P.comap S.subtype, hPo.preimage continuous_subtype_val, ?_, ?_⟩
  · have hemb : Topology.IsClosedEmbedding (Subtype.val : S → G) := hS.isClosedEmbedding_subtypeVal
    exact hemb.isCompact_preimage hPc
  · intro x hx
    exact hsub (hPW hx)

theorem small_pow {z : ℂ} (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1 / 2) : z = 1 :=
  by apply _root_.UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near <;> assumption

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

open GlobalTheory.CompanionTheory.SW.Core in
theorem hasCO_Af (F : Type) [Field F] [NumberField F] : HasCO (Af F) := by
  obtain ⟨h1, h2, h3, hOc, hOo, -, -, hB, -, hNo⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hadd : ∀ x ∈ Oh F, ∀ y ∈ Oh F, x + y ∈ Oh F := fun x hx y hy v =>
    add_mem (hx v) (hy v)
  have hneg : ∀ x ∈ Oh F, -x ∈ Oh F := fun x hx v => neg_mem (hx v)
  have hz : (0 : Af F) ∈ Oh F := fun v => zero_mem _
  intro W hW
  obtain ⟨N, hN, hNW⟩ := hB W hW
  let P : AddSubgroup (Af F) :=
    { carrier := {x | ∃ y ∈ Oh F, x = (N : Af F) * y}
      zero_mem' := ⟨0, hz, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, hadd x hx y hy, by ring⟩
      neg_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨-x, hneg x hx, by ring⟩ }
  refine ⟨P, hNo N hN, ?_, ?_⟩
  · have : (P : Set (Af F)) = (fun y => (N : Af F) * y) '' Oh F := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [this]
    exact hOc.image (continuous_const.mul continuous_id)
  · rintro _ ⟨y, hy, rfl⟩
    exact hNW y hy

theorem psiFin_add (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (x y : Af F) :
    psiFin F ψ (x + y) = psiFin F ψ x * psiFin F ψ y := by
  have : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y :=
    Prod.ext (show (0 : Ainf F) = 0 + 0 by simp) rfl
  simp only [psiFin]
  rw [this, AddChar.map_add_eq_mul]

theorem psiFin_trivial (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : ∃ V : AddSubgroup (Af F), IsOpen (V : Set (Af F)) ∧
      ∀ y ∈ V, psiFin F ψ y = 1 := by
  have hc : Continuous (psiFin F ψ) := by
    have : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
    exact hψ.1.comp this
  have h0 : psiFin F ψ 0 = 1 := by
    have : pairA F 0 (0 : Af F) = 0 := rfl
    simp [psiFin, this]
  have hB : {y | ‖psiFin F ψ y - 1‖ < 1 / 2} ∈ 𝓝 (0 : Af F) := by
    have : IsOpen {y | ‖psiFin F ψ y - 1‖ < 1 / 2} :=
      isOpen_lt ((hc.sub continuous_const).norm) continuous_const
    exact this.mem_nhds (by simp [h0])
  obtain ⟨P, hPo, -, hPB⟩ := hasCO_Af F _ hB
  refine ⟨P, hPo, fun y hy => small_pow fun k => ?_⟩
  have hk : psiFin F ψ (k • y) = psiFin F ψ y ^ k := by
    induction k with
    | zero =>
      simpa using h0
    | succ k ih =>
      rw [succ_nsmul, psiFin_add, ih, pow_succ]
  rw [← hk]
  exact hPB (P.nsmul_mem hy k)

theorem hasCO_herm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n : ℕ) : HasCO (HermR (Af F) σ n) := by
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨-, -, -, -, -, -, hh, -, hcl, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let c : (Af F ⊗[F] E) →+ (Fin (Module.finrank F E) → Af F) :=
    { toFun := fun y k => (Algebra.TensorProduct.basis (Af F) b).repr y k
      map_zero' := by
        funext k
        simp
      map_add' := by
        intro x y
        funext k
        simp }
  have hT : HasCO (Af F ⊗[F] E) :=
    HasCO.comap (HasCO.pi fun _ => hasCO_Af F) c (hh _ b)
  have hM : HasCO (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    HasCO.pi (G := fun _ : Fin n => Fin n → Af F ⊗[F] E) fun _ => HasCO.pi fun _ => hT
  exact hM.sub _ (hcl n)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

theorem tube_zero {H Y A : Type} [AddGroup H] [TopologicalSpace H] [TopologicalSpace Y]
    [TopologicalSpace A] (ph : H → Y → A) (hph : Continuous fun p : H × Y => ph p.1 p.2)
    {V : Set A} (hV : IsOpen V) (h0 : ∀ X, ph 0 X ∈ V) {K : Set Y} (hK : IsCompact K) :
    ∃ W ∈ 𝓝 (0 : H), ∀ u ∈ W, ∀ X ∈ K, ph u X ∈ V := by
  have hsub : ({0} : Set H) ×ˢ K ⊆ (fun p : H × Y => ph p.1 p.2) ⁻¹' V := by
    rintro ⟨u, X⟩ ⟨hu, -⟩
    have hu0 : u = 0 := hu
    subst hu0
    exact h0 X
  obtain ⟨W, W', hWo, -, h0W, hKW, hWW⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hV.preimage hph) hsub
  exact ⟨W, hWo.mem_nhds (h0W rfl), fun u hu X hX => hWW (Set.mk_mem_prod hu (hKW hX))⟩

set_option maxHeartbeats 1000000 in

theorem starLoc_periodic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ U : AddSubgroup (HermR (Af F) σ n), IsOpen (U : Set (HermR (Af F) σ n)) ∧
      IsCompact (U : Set (HermR (Af F) σ n)) ∧
      ∀ b, ∀ u ∈ U, starLoc (Af F) σ J (psiFin F ψ) μ Q (b + u) = starLoc (Af F) σ J (psiFin F ψ) μ Q b := by
  intro F E _ _ _ _ _ σ hσ M J n ψ hψ μ _ Q hQ
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨t1, -, -, -, -, htr, -, -, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := t1
  obtain ⟨V, hVo, hV⟩ := psiFin_trivial F ψ hψ
  let ph : HermR (Af F) σ n → (Fin n → Fin M → Af F ⊗[F] E) → Af F := fun u X =>
    algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace ((u : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gramR (Af F) σ J X))
  have hph : Continuous fun p : HermR (Af F) σ n × (Fin n → Fin M → Af F ⊗[F] E) => ph p.1 p.2 := by
    refine continuous_const.mul (htr.comp (Continuous.matrix_trace (Continuous.matrix_mul ?_ ?_)))
    · exact continuous_subtype_val.comp continuous_fst
    · exact (hG n M J).comp continuous_snd
  have hK : IsCompact (tsupport Q) := hQ.2
  have h0 : ∀ X, ph 0 X ∈ (V : Set (Af F)) := fun X => by
    simp [ph, V.zero_mem]
  obtain ⟨W, hW0, hWW⟩ := tube_zero ph hph hVo h0 hK
  obtain ⟨U, hUo, hUc, hUW⟩ := hasCO_herm F E σ hσ n W hW0
  refine ⟨U, hUo, hUc, fun b u hu => ?_⟩
  unfold starLoc
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  by_cases hX : X ∈ tsupport Q
  · have hsplit : ph (b + u) X = ph b X + ph u X := by
      simp only [ph, AddSubgroup.coe_add, add_mul, Matrix.trace_add, map_add, mul_add]
    have hm : ph u X ∈ V := hWW u (hUW (SetLike.mem_coe.2 hu)) X hX
    have h1 : psiFin F ψ (ph u X) = 1 := hV (ph u X) hm
    change Q X * psiFin F ψ (ph (b + u) X) = Q X * psiFin F ψ (ph b X)
    rw [hsplit, psiFin_add, h1, mul_one]
  · have hq : Q X = 0 := image_eq_zero_of_notMem_tsupport hX
    simp [hq]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period
