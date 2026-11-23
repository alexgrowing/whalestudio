import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusionsStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical ComplexConjugate

namespace PositivityTheory.Rg.BcB.CG

theorem trace_mul_ent {n : ℕ} (M : KMod n) (A B : M.V →L[ℂ] M.V) :
    LinearMap.trace ℂ M.V ((A * B : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) = ∑ i, ∑ j, ent M A i j * ent M B j i := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ M.V)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((A * B : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) (stdOrthonormalBasis ℂ M.V i) =
      A (∑ j, inner ℂ (stdOrthonormalBasis ℂ M.V j) (B (stdOrthonormalBasis ℂ M.V i)) • stdOrthonormalBasis ℂ M.V j) := by
    rw [(stdOrthonormalBasis ℂ M.V).sum_repr']; rfl
  rw [h, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, ent, ent, mul_comm]

theorem phiOf_eq {n : ℕ} (M : KMod n) (Tθ : M.V →L[ℂ] M.V) (k : Mat n → (M.V →L[ℂ] M.V)) (y : G n) :
    phiOf M Tθ k y = ∑ p, ∑ q, ent M (k y.val) p q * ent M Tθ q p :=
  trace_mul_ent M _ _

theorem ent_adjoint {n : ℕ} (M : KMod n) [CompleteSpace M.V] (A : M.V →L[ℂ] M.V) (i j : Ix M) :
    ent M (ContinuousLinearMap.adjoint A) i j = conj (ent M A j i) := by
  simp only [ent]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem sum_pair {α β : Type} [Fintype α] [Fintype β] (X : α → α → ℂ) (Y : β → β → ℂ) :
    ∑ i : α × β, ∑ j : α × β, X i.1 j.1 * Y i.2 j.2 = (∑ p, ∑ q, X p q) * ∑ p, ∑ q, Y p q := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem sum_io {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ] (A A' : α → α → ℂ) (B B' : β → β → ℂ)
    (C D : κ → κ → ℂ) :
    ∑ i : (α × β) × κ, ∑ j : (α × β) × κ,
        A i.1.1 j.1.1 * B i.1.2 j.1.2 * C i.2 j.2 * (A' j.1.1 i.1.1 * B' j.1.2 i.1.2 * D j.2 i.2) =
      (∑ p, ∑ q, A p q * A' q p) * (∑ p, ∑ q, B p q * B' q p) * ∑ x, ∑ y, C x y * D y x := by
  calc _ = ∑ i : (α × β) × κ, ∑ j : (α × β) × κ,
          (A i.1.1 j.1.1 * A' j.1.1 i.1.1 * (B i.1.2 j.1.2 * B' j.1.2 i.1.2)) * (C i.2 j.2 * D j.2 i.2) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ p : α × β, ∑ q : α × β, A p.1 q.1 * A' q.1 p.1 * (B p.2 q.2 * B' q.2 p.2)) * ∑ x, ∑ y, C x y * D y x :=
        sum_pair (fun p q : α × β => A p.1 q.1 * A' q.1 p.1 * (B p.2 q.2 * B' q.2 p.2)) (fun x y => C x y * D y x)
    _ = _ := by
        rw [sum_pair (fun p q => A p q * A' q p) (fun p q => B p q * B' q p)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem prod_sum_ent (M : Mods E n) (A B : Ops M) :
    ∏ v, (∑ p, ∑ q, ent (M v) (A v) p q * ent (M v) (B v) q p) =
      ∑ P : IxA M, ∑ Q : IxA M, (∏ v, ent (M v) (A v) (P v) (Q v)) * ∏ v, ent (M v) (B v) (Q v) (P v) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun Q _ => ?_
  exact Finset.prod_mul_distrib

theorem tensTr : TensTr := by
  intro E _ _ _ a b Ma Mb κ _ ka kb Ta Tb ψ N g
  have ha := prod_sum_ent Ma (fun v => ka v (gInf v g.1).val) Ta
  have hb := prod_sum_ent Mb (fun v => kb v (gInf v g.2).val) Tb
  simp only [F.trM, tens, opM, entA, phiOf_eq]
  rw [ha, hb]
  exact sum_io (α := IxA Ma) (β := IxA Mb) (κ := κ)
    (fun P Q : IxA Ma => ∏ v, ent (Ma v) (ka v (gInf v g.1).val) (P v) (Q v))
    (fun Q P : IxA Ma => ∏ v, ent (Ma v) (Ta v) (Q v) (P v))
    (fun P Q : IxA Mb => ∏ v, ent (Mb v) (kb v (gInf v g.2).val) (P v) (Q v))
    (fun Q P : IxA Mb => ∏ v, ent (Mb v) (Tb v) (Q v) (P v)) (fun x y : κ => ψ x y (hFin g)) (fun y x : κ => N y x)

theorem gInf_eq (v : InfinitePlace E) (g : GA E n) :
    gInf v g = GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v)
      (GeneralLinearGroup.map (pInf E) g) := rfl

theorem continuous_gInf (v : InfinitePlace E) : Continuous (gInf (E := E) (n := n) v) := by
  have h : Continuous (GeneralLinearGroup.map (n := Fin n) (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v)) :=
    Continuous.units_map _ (by exact continuous_id.matrix_map (continuous_apply v))
  exact (h.comp (GlobalTheory.T.continuous_GL_adelic_projections_inclusions E n).1).congr fun g => (gInf_eq v g).symm

theorem continuous_hFin : Continuous (hFin (E := E) (a := a) (b := b)) :=
  ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.1.comp continuous_fst).prodMk ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.1.comp continuous_snd)

theorem hFin_inv (g : H E a b) : hFin g⁻¹ = (hFin g)⁻¹ :=
  Prod.ext (map_inv (gFin (E := E) (n := a)) g.1) (map_inv (gFin (E := E) (n := b)) g.2)

def ofComps (y : InfinitePlace E → G n) : GL (Fin n) (Cinf E) :=
  Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm y)

theorem continuous_ofComps : Continuous (ofComps (E := E) (n := n)) := by
  have hc : Continuous fun x : InfinitePlace E → Mat n =>
      (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm x :=
    continuous_matrix fun i j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  exact (Continuous.units_map _ hc).comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E => Mat n)).symm.continuous

theorem ofComps_gInf (g : GA E n) : ofComps (fun v => gInf v g) = GeneralLinearGroup.map (pInf E) g :=
  Units.ext (Matrix.ext fun _ _ => funext fun _ => rfl)

theorem hasCompactSupport_of_section {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {F : X → ℂ}
    (p : X → Y) (s : Y → X) (hs : Continuous s) (hsp : ∀ x, s (p x) = x) {K : Set Y} (hK : IsCompact K)
    (hF : ∀ x, F x ≠ 0 → p x ∈ K) : HasCompactSupport F :=
  HasCompactSupport.intro (hK.image hs) fun x hx => by
    by_contra h
    exact hx ⟨p x, hF x h, hsp x⟩

def ofParts (y : ((InfinitePlace E → G a) × (InfinitePlace E → G b)) × Hf E a b) : H E a b :=
  (infGL E a (ofComps y.1.1) * finGL E a y.2.1, infGL E b (ofComps y.1.2) * finGL E b y.2.2)

theorem continuous_ofParts : Continuous (ofParts (E := E) (a := a) (b := b)) :=
  (((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.2.1.comp (continuous_ofComps.comp (continuous_fst.comp continuous_fst))).mul
      ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.2.2.comp (continuous_fst.comp continuous_snd))).prodMk
    (((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.2.1.comp (continuous_ofComps.comp (continuous_snd.comp continuous_fst))).mul
      ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.2.2.comp (continuous_snd.comp continuous_snd)))

theorem ofParts_parts (g : H E a b) : ofParts ((fun v => gInf v g.1, fun v => gInf v g.2), hFin g) = g := by
  refine Prod.ext ?_ ?_
  · show infGL E a (ofComps fun v => gInf v g.1) * finGL E a (gFin g.1) = g.1
    rw [ofComps_gInf]; exact infGL_mul_finGL g.1
  · show infGL E b (ofComps fun v => gInf v g.2) * finGL E b (gFin g.2) = g.2
    rw [ofComps_gInf]; exact infGL_mul_finGL g.2

theorem entA_adjK (M : Mods E n) (k : Kers M) (i j : IxA M) (g : GA E n) :
    entA (adjK k) i j g = conj (entA k j i g⁻¹) := by
  simp only [entA, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have e : (gInf v g⁻¹).val = (gInf v g).val⁻¹ := by rw [map_inv]; exact Matrix.coe_units_inv _
  rw [e]
  have := FiniteDimensional.complete ℂ (M v).V
  exact ent_adjoint (M v) _ (i v) (j v)

theorem tens_entry {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [MeasurableSpace (G a)] [MeasurableSpace (G b)]
    {μa : Measure (G a)} {μb : Measure (G b)} {ka : Kers Ma} {kb : Kers Mb} {va vb} {T : ℝ}
    {ψ : Matrix κ κ (Hf E a b → ℂ)} (hA : IsMults μa ka va T) (hB : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (i j : Io Ma Mb κ) : Continuous (tens ka kb ψ i j) ∧ HasCompactSupport (tens ka kb ψ i j) := by
  have cA : ∀ v, Continuous fun y : G a => ent (Ma v) (ka v y.val) (i.1.1 v) (j.1.1 v) := fun v =>
    (mult_ent (hA v) _ _).1
  have cB : ∀ v, Continuous fun y : G b => ent (Mb v) (kb v y.val) (i.1.2 v) (j.1.2 v) := fun v =>
    (mult_ent (hB v) _ _).1
  refine ⟨?_, ?_⟩
  · exact ((continuous_finsetProd _ fun v _ => (cA v).comp ((continuous_gInf v).comp continuous_fst)).mul
      (continuous_finsetProd _ fun v _ => (cB v).comp ((continuous_gInf v).comp continuous_snd))).mul
      ((hψ i.2 j.2).1.comp continuous_hFin)
  · refine hasCompactSupport_of_section (fun g : H E a b => ((fun v => gInf v g.1, fun v => gInf v g.2), hFin g))
      ofParts continuous_ofParts ofParts_parts
      (K := (Set.univ.pi (fun v => tsupport fun y : G a => ent (Ma v) (ka v y.val) (i.1.1 v) (j.1.1 v)) ×ˢ
        Set.univ.pi (fun v => tsupport fun y : G b => ent (Mb v) (kb v y.val) (i.1.2 v) (j.1.2 v))) ×ˢ
        tsupport (ψ i.2 j.2))
      (((isCompact_univ_pi fun v => (mult_ent (hA v) _ _).2).prod
        (isCompact_univ_pi fun v => (mult_ent (hB v) _ _).2)).prod (hψ i.2 j.2).2) fun g hg => ?_
    have hg' : entA ka i.1.1 j.1.1 g.1 * entA kb i.1.2 j.1.2 g.2 * ψ i.2 j.2 (hFin g) ≠ 0 := hg
    obtain ⟨⟨h1, h2⟩, h3⟩ := mul_ne_zero_iff.1 hg' |>.imp_left mul_ne_zero_iff.1
    refine ⟨⟨fun v _ => subset_tsupport _ ?_, fun v _ => subset_tsupport _ ?_⟩, subset_tsupport _ h3⟩
    · exact Finset.prod_ne_zero_iff.1 h1 v (Finset.mem_univ v)
    · exact Finset.prod_ne_zero_iff.1 h2 v (Finset.mem_univ v)

theorem tensTest : TensTest := by
  intro E _ _ _ a b _ _ _ _ μa _ μb _ Ma Mb κ _ ka kb va vb T ψ hA hB hψ
  refine ⟨fun i j => tens_entry hA hB hψ i j, ?_⟩
  funext i j y
  show starRingEnd ℂ (tens ka kb ψ j i y⁻¹) = tens (adjK ka) (adjK kb) (adjF ψ) i j y
  simp only [tens, adjF, entA_adjK, map_mul, hFin_inv, Prod.fst_inv, Prod.snd_inv]

end PositivityTheory.Rg.BcB.CG

end
