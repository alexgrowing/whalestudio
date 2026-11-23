import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionOfTransversal
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.HenselZero
open GlobalTheory.KeyKa.EtBaseChange

section Via
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}

theorem map_mem_nonzeroLocus_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (hy : y ∈ Out.nonzeroLocus s') : φ y ∈ Out.nonzeroLocus s := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨k, hk⟩ := exists_chart x.P.isLB (φ y)
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have hV : y ∈ (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i := ⟨mem_pull.2 hk, x'.P.A.left.basicOpen_le _ hi⟩
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    refine (congrArg x'.P.A.left.basicOpen e).ge ((Scheme.basicOpen_mul _ _ _).ge ⟨?_, ?_⟩)
    · exact (Scheme.basicOpen_of_isUnit _ ((Units.isUnit (w.s (fun _ => k, i))).pow l)).ge hV
    · exact (Scheme.basicOpen_res _ _ _).ge ⟨hV, hi⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)).le h1).2⟩

theorem exists_gs_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (c : x.P.L.ι) (c' : x'.P.L.ι) (h : φ y ∈ x.P.L.U c) (h' : y ∈ x'.P.L.U c') :
    ∃ u, IsUnit u ∧ gs φ y (x.P.L.U c) (s.f c) = u * gs (𝟙 _) y (x'.P.L.U c') (s'.f c') := by
  have hle : (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' ≤ φ ⁻¹ᵁ x.P.L.U c := fun y hy => mem_pull.1 hy.1
  have hV : (𝟙 x'.P.A.left : _ ⟶ _) y ∈ (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' := ⟨mem_pull.2 h, h'⟩
  have e := congrArg (gs (𝟙 _) y _) (hs (fun _ => c) c' hle)
  have e₁ := (gs_res (𝟙 _) y hle hV ((φ.app _).hom (s.f c))).trans (gs_pull (𝟙 _) φ y _ h (s.f c))
  rw [Category.id_comp] at e₁
  refine ⟨_, ?_, e₁.symm.trans (e.trans ((gs_mul _ _ _ hV _ _).trans
    (congrArg (_ * ·) (gs_res (𝟙 _) y inf_le_right hV _))))⟩
  rw [gs_eq _ _ _ hV]
  exact (((Units.isUnit (w.s (fun _ => c, c'))).pow l).map _).map _

end Via

theorem exists_lift_point {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {x : KeyIn O} {xk : KeyIn (IsLocalRing.ResidueField O)} {φ w}
    {n : ℕ} (hg : xk.P.g = x.P.g) {s : Fin x.P.g → RR x n} {sk : Fin xk.P.g → RR xk n}
    (hvia : KeyVia xk x (IsLocalRing.residue O) φ w) (hs : ∀ i, SecVia xk x φ w (sk i) (s (i.cast hg)))
    (zk : Pt xk) (c' : xk.P.L.ι) (h₁ : ⊤ ≤ zk.left ⁻¹ᵁ xk.P.L.U c')
    (h₂ : ∀ i, valT (T := IsLocalRing.ResidueField O) zk.left (xk.P.L.U c') ((sk i).f c') = 0)
    (h₃ : IsUnit (jac xk sk zk c')) :
    ∃ (z : Pt x) (c : x.P.L.ι), spMap (IsLocalRing.residue O) ≫ z.left = zk.left ≫ φ ∧ ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧
      (∀ i, valT (T := O) z.left (x.P.L.U c) ((s i).f c) = 0) ∧ IsUnit (jac x s z c) ∧
      ∀ (y : x.P.A.left) (pt : Sp (IsLocalRing.ResidueField O)), y ⤳ φ (zk.left pt) →
        (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ r : Sp O, z.left r = y := by
  obtain ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ := hvia
  have := x.P.isAb.smooth
  let pt : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint _
  have hpt : ∀ r : Sp (IsLocalRing.ResidueField O), r = pt := fun r =>
    Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField O)) _ _
  obtain ⟨c, hc⟩ := exists_chart x.P.isLB (φ (zk.left pt))
  have hc' : zk.left pt ∈ xk.P.L.U c' := h₁ (x := pt) trivial
  have hφ : ⊤ ≤ (zk.left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun r _ => by
    obtain rfl := hpt r
    exact hc
  have hW := le_inf_pull (T := IsLocalRing.ResidueField O) zk.left c c' hφ h₁
  let u := Units.map (valH (T := IsLocalRing.ResidueField O) zk.left _ hW).toMonoidHom (w.s (fun _ => c, c'))
  have hu : valT (T := IsLocalRing.ResidueField O) zk.left ((x.P.L.pull φ).U (fun _ => c) ⊓ xk.P.L.U c')
      (w.s (fun _ => c, c')).val = u := valT_eq _ _ hW _
  have hd : (Matrix.of fun i k => (valT (T := DualNumber (IsLocalRing.ResidueField O))
      (((toUnit (epsR _) ≫ zk) * xk.v k).left ≫ φ) (x.P.L.U c) ((s (i.cast hg)).f c)).snd).det ≠ 0 := by
    refine fun h => mul_ne_zero (pow_ne_zero (Fintype.card (Fin xk.P.g)) (pow_ne_zero n u.ne_zero)) h₃.ne_zero
      ((Matrix.det_smul _ _).symm.trans (Eq.trans ?_ h))
    congr 1
    ext i k
    have l₂ := translate_le zk (xk.v k) (xk.basis.1 _) h₁
    have l₃ : ⊤ ≤ (((toUnit (epsR _) ≫ zk) * xk.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U c :=
      translate_le zk (xk.v k) (xk.basis.1 _) (U := φ ⁻¹ᵁ x.P.L.U c) hφ
    have e := valT_via (T := DualNumber (IsLocalRing.ResidueField O)) (hs i) _ c c' l₃ l₂
    refine Eq.symm ((congrArg TrivSqZeroExt.snd e).trans ?_)
    refine (snd_pow_mul _ _ _ ((fst_valT_translate zk (xk.v k) (xk.basis.1 _) h₁ _).trans (h₂ i))).trans ?_
    exact congrArg (· ^ n * _) ((fst_valT_translate zk (xk.v k) (xk.basis.1 _) hW _).trans hu)
  obtain ⟨z₀, hz₁, hz₂, hz₃, hz₄⟩ := exists_section_of_transversal hp.1 zk.left (Over.w zk) pt hc
    (fun i : Fin xk.P.g => (s (i.cast hg)).f c)
    (fun i => (valT_via (T := IsLocalRing.ResidueField O) (hs i) zk.left c c' hφ h₁).trans
      (mul_eq_zero_of_right _ (h₂ i)))
    (by
      rw [← (jac_ne_zero_iff_span_eq_maximalIdeal _ xk n sk zk c' pt h₁ h₂).1 h₃.ne_zero]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨v, hv, e⟩ := exists_gs_via (hs i) (zk.left pt) c c' hc hc'
      exact (Ideal.unit_mul_mem_iff_mem _ hv).1 (Ideal.subset_span ⟨i, e⟩))
    (fun k => ((toUnit (epsR _) ≫ zk) * xk.v k).left)
    (fun k => fst_comp_translate zk (xk.v k) (xk.basis.1 _)) (fun k => Over.w ((toUnit (epsR _) ≫ zk) * xk.v k)) hd
  let z : Pt x := Over.homMk z₀ hz₁
  have hz : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c := (Scheme.preimage_eq_top_of_closedPoint_mem z₀ (by
    rw [← IsLocalRing.comap_closedPoint (IsLocalRing.residue O)]
    exact (congrArg (fun g => g pt ∈ x.P.L.U c) hz₂).ge hc)).ge
  refine ⟨z, c, hz₂, hz, fun i => hz₃ (i.cast hg.symm), ?_, fun y r hy hy' => ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    refine fun h => hd (Eq.trans ?_ h)
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg)]
    congr 1
    ext i k
    have e := translate_comp hp F hF₁ z zk hz₂.symm (x.v (k.cast hg)) (xk.v k) (hv k)
    have l₁ := translate_le z (x.v (k.cast hg)) (x.basis.1 _) hz
    have e₂ := (congrArg (fun q => valT (T := DualNumber (IsLocalRing.ResidueField O)) q (x.P.L.U c)
      ((s (i.cast hg)).f c)) e).trans (valT_spMap F _ l₁ _)
    exact (congrArg TrivSqZeroExt.snd e₂).trans (snd_map _ F hF₁ hF₂ _)
  · obtain rfl := hpt r
    exact hz₄ y hy fun i h => hy' (i.cast hg) (TopologicalSpace.Opens.mem_iSup.2 ⟨c, h⟩)

end GlobalTheory.HenselZero

open GlobalTheory.HenselZero in

theorem GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (xk : KeyIn (IsLocalRing.ResidueField O)) φ w (n d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), KeyVia xk x (IsLocalRing.residue O) φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  intro O _ _ _ _ x xk φ w n d hg s sk zk chk hvia hs ⟨h₁, h₂, h₃, h₄, h₅⟩
  choose z ch hz₀ hz₁ hz₂ hz₃ hz₄ using fun a => exists_lift_point hg hvia hs (zk a) (chk a) (h₁ a) (h₂ a) (h₃ a)
  obtain ⟨_, _, _, ⟨hp, -⟩, -⟩ := hvia
  have := x.P.isAb.proper
  have := isClosedImmersion_fibre hp
  let pt : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint _
  have hcp : spMap (IsLocalRing.residue O) pt = IsLocalRing.closedPoint O :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have hw : ∀ a, (z a).left ≫ x.P.A.hom = 𝟙 (Sp O) := fun a => Over.w (z a)
  have hzc : ∀ a, (z a).left (IsLocalRing.closedPoint O) = φ ((zk a).left pt) := fun a =>
    (congrArg (z a).left hcp).symm.trans (congrArg (fun g => g pt) (hz₀ a))
  refine ⟨z, ch, hz₁, hz₂, hz₃, fun a a' h r e => h₄ a a' h pt (φ.isClosedEmbedding.injective ?_), fun y hy => ?_⟩
  · have : IsClosedImmersion ((z a').left ≫ x.P.A.hom) := by
      rw [hw]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp O) : Sp O ⟶ Sp O))
    have := IsClosedImmersion.of_comp (z a').left x.P.A.hom
    obtain ⟨r', hr'⟩ := ((IsLocalRing.specializes_closedPoint r).map (z a).left.continuous).mem_closed
      (z a').left.isClosedEmbedding.isClosed_range ⟨r, e.symm⟩
    have e₁ : r' = IsLocalRing.closedPoint O :=
      (congrArg (fun g => g r') (hw a')).symm.trans ((congrArg x.P.A.hom hr').trans
        (congrArg (fun g => g (IsLocalRing.closedPoint O)) (hw a)))
    rw [← hzc, ← hzc, ← hr', e₁]
  · obtain ⟨y₀, hy₀, e⟩ := (IsLocalRing.specializes_closedPoint (x.P.A.hom y)).mem_closed
      (x.P.A.hom.isClosedMap _ (isClosed_closure (s := {y}))) ⟨y, subset_closure rfl, rfl⟩
    have hsp : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
    obtain ⟨y', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hp y₀ pt (e.trans hcp.symm)
    obtain ⟨a, r, rfl⟩ := h₅ y' fun i h => hy (i.cast hg)
      (hsp.mem_open (Out.nonzeroLocus _).isOpen (map_mem_nonzeroLocus_via (hs i) y' h))
    exact ⟨a, hz₄ a y r hsp hy⟩

end
