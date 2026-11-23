import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GeoModel
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UT
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  have h : Function.Injective (OO p).subtype := Subtype.val_injective
  have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  exact this

theorem toG_over (u : ρ.UTest p y₀) (a : u.PtC) : u.toG a ≫ u.G.hom = gPt p ≫ spMap u.j := by
  have h := Over.w a
  simp only [ThetaSys.Real.UTest.toG, Category.assoc, pullback.condition]
  rw [← Category.assoc]
  refine (congrArg (· ≫ jK u.V) h).trans ?_
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem exists_intGood (u : ρ.UTest p y₀) :
    ∃ J, u.IntGood J ∧ ∀ z, Good u.D.toPre.P.L z J := by
  classical
  have hsep : IsSeparated u.D.toPre.P.A.hom := by
    have := u.D.toPre.P.isAb.proper
    infer_instance
  have hc : ∀ x : u.D.toPre.P.A.left, ∃ i, x ∈ u.D.toPre.P.L.U i := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [u.D.toPre.P.isLB.cover]; trivial)
  choose ch hch using hc
  have := isDominant_gPt p
  let P : (Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left) → Prop := fun φ =>
    ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧ gPt p ≫ ψ = φ
  let J : (Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left) → u.D.toPre.P.L.ι := fun φ =>
    if h : P φ then ch (h.choose (cPt p)) else ch (φ (IsLocalRing.closedPoint _))
  have key : ∀ (ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left) (w : Sp (OO p)), ψ w ∈ u.D.toPre.P.L.U (ch (ψ (cPt p))) :=
    fun ψ w => ((IsLocalRing.specializes_closedPoint w).map ψ.continuous).mem_open
      (u.D.toPre.P.L.U _).isOpen (hch _)
  refine ⟨J, fun ψ hψ => ?_, fun z φ => ?_⟩
  · have h : P (gPt p ≫ ψ) := ⟨ψ, hψ, rfl⟩
    have e : h.choose = ψ :=
      ext_of_isDominant_of_isSeparated u.D.toPre.P.A.hom (h.choose_spec.1.trans hψ.symm) (gPt p) h.choose_spec.2
    have hJ : J (gPt p ≫ ψ) = ch (ψ (cPt p)) := by
      simp only [J]; rw [dif_pos h, e]
    intro w _
    show ψ w ∈ u.D.toPre.P.L.U (J (gPt p ≫ ψ))
    rw [hJ]; exact key ψ w
  · show φ z ∈ u.D.toPre.P.L.U (J φ)
    by_cases h : P φ
    · have hJ : J φ = ch (h.choose (cPt p)) := by simp only [J]; rw [dif_pos h]
      rw [hJ]
      have e : φ z = h.choose (gPt p z) := by
        conv_lhs => rw [← h.choose_spec.2]
        rfl
      rw [e]; exact key _ _
    · have hJ : J φ = ch (φ (IsLocalRing.closedPoint _)) := by simp only [J]; rw [dif_neg h]
      rw [hJ]
      have e : z = IsLocalRing.closedPoint (PadicAlgCl p) := Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _
      rw [e]; exact hch _

theorem gtN_unique (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν ν' : u.D.toPre.X → ℝ)
    (h : u.GtN g ν) (h' : u.GtN g ν') : ν = ν' := by
  obtain ⟨J, hJ, -⟩ := exists_intGood u
  funext χ
  have := (h J hJ χ).symm.trans (h' J hJ χ)
  simpa using this

theorem j_mem_max (u : ρ.UTest p y₀) (x : u.V) (hx : x ∈ IsLocalRing.maximalIdeal u.V) :
    u.j x ∈ IsLocalRing.maximalIdeal (OO p) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ x) * (y : PadicAlgCl p) = 1 :=
    congrArg Subtype.val hy
  have h2 : (y : PadicAlgCl p) = algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ x)⁻¹ := by
    rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right h1
  obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V _ x)⁻¹).1 (h2 ▸ (mem_OO_iff _).1 y.2)
  have h0 : algebraMap u.V (FractionRing u.V) x ≠ 0 := fun h => by simp [h] at h1
  refine IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]

theorem lev_ne_top (u : ρ.UTest p y₀) (e : ℕ) : u.lev e ≠ ⊤ := by
  refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (OO p)).ne_top ?_
  rw [Ideal.map_le_iff_le_comap]
  exact fun x hx => j_mem_max u x (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)

theorem exists_level_point (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left) (hc : c ≫ u.G.hom = spMap u.j) (e : ℕ) :
    ∃ ce : Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left,
      ce ≫ (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c := by
  refine ⟨pullback.lift (spMap (Ideal.Quotient.mk (u.lev e)) ≫ c)
    (spMap (Ideal.quotientMap (u.lev e) u.j Ideal.le_comap_map)) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, hc]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem ser_int (t : ρ.GeoTest p y₀) (a : t.u.PtC) (w : S.J → PadicAlgCl p)
    (hw : Crd (t.u.H S.N) t.σ (t.u.toG a) w) :
    ∃ ν : t.u.D.toPre.X →+ ℝ, Ser t.l.q S.N t.cls w ν ∧
      ((∃ m, ∀ α, ν α = QuadraticMap.polar t.l.q m α) → t.u.Int a) :=
  t.mod.ser _ (toG_over t.u a) w hw

theorem hasU_of_hasGeo (h : ρ.HasGeo) : ρ.HasU := fun p _ y₀ hy Fs =>
  let ⟨t, ht⟩ := h p y₀ hy Fs
  ⟨t.u, t.l, t.τ, t.mt, ht⟩

theorem hasTests_of_hasU (h : ρ.HasU) : S.HasTests := fun p _ y₀ hy =>
  let ⟨_, _, τ, _⟩ := h p y₀ hy ∅
  ⟨τ⟩

theorem basis_rep (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ) {J : Type} [Fintype J] (σ : J → (u.H k).Sec)
    (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α) (h : u.Basis l k σ cls f) (α : u.D.toPre.X) :
    ∃! β, β ∈ Set.range cls ∧ ∃ m, α = β + k • m := by
  obtain ⟨-, h2, h3, -⟩ := h
  obtain ⟨i, m, hi⟩ := h3 α
  refine ⟨cls i, ⟨⟨i, rfl⟩, m, hi⟩, ?_⟩
  rintro _ ⟨⟨i', rfl⟩, m', hi'⟩
  refine h2 i' i ⟨m - m', ?_⟩
  rw [smul_sub, ← add_sub_assoc, ← hi, hi', add_sub_cancel_right]

theorem norm_unit {X : Scheme.{0}} (ψ : Sp (OO p) ⟶ X) (U : X.Opens) (h : ⊤ ≤ ψ ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    ‖Geo.Tor.valR (gPt p ≫ ψ) U f.val‖ = 1 := by
  rw [GlobalTheory.Points.valR_spMap_comp _ ψ U h]
  have hu : IsUnit (Geo.Tor.valR ψ U f.val) := by
    rw [GlobalTheory.Points.valR_eq ψ U h]; exact f.isUnit.map _
  have h1 := (not_isUnit_OO_iff (Geo.Tor.valR ψ U f.val)).not.1 (not_not.2 hu)
  exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _)) (not_lt.1 h1)

theorem norm_indep {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Sp (OO p) ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L (fun k => gPt p ≫ ψ k) ε)) (ht : t.IsGen) (j j' : K → L.ι)
    (hj : ∀ k, ⊤ ≤ ψ k ⁻¹ᵁ L.U (j k)) (hj' : ∀ k, ⊤ ≤ ψ k ⁻¹ᵁ L.U (j' k)) :
    ‖valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s j).val‖ = ‖valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s j').val‖ ∧
      valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s j).val ≠ 0 := by
  have a : ⊤ ≤ (𝟙 (Sp (PadicAlgCl p))) ⁻¹ᵁ LB.wchart L (fun k => gPt p ≫ ψ k) j :=
    fun w _ => Set.mem_iInter.2 fun k => hj k (x := gPt p w) trivial
  have a' : ⊤ ≤ (𝟙 (Sp (PadicAlgCl p))) ⁻¹ᵁ LB.wchart L (fun k => gPt p ≫ ψ k) j' :=
    fun w _ => Set.mem_iInter.2 fun k => hj' k (x := gPt p w) trivial
  have b : ⊤ ≤ (𝟙 (Sp (PadicAlgCl p))) ⁻¹ᵁ
      (LB.wchart L (fun k => gPt p ≫ ψ k) j ⊓ LB.wchart L (fun k => gPt p ≫ ψ k) j') :=
    fun w _ => ⟨a (x := w) trivial, a' (x := w) trivial⟩
  refine ⟨?_, ?_⟩
  · let E := Units.map (GlobalTheory.Points.valMap (𝟙 (Sp (PadicAlgCl p))) _ b).hom.toMonoidHom
    let Nn : (PadicAlgCl p)ˣ →* ℝˣ := Units.map (normHom (α := PadicAlgCl p)).toMonoidHom
    have e := congrArg (fun x => Nn (E x)) (ht j j')
    have hg : Nn (E ((LB.LinComb L (fun k => gPt p ≫ ψ k) ε).g j j')) = 1 := by
      show Nn (E (∏ k, _)) = 1
      rw [map_prod, map_prod]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [map_zpow, map_zpow]
      have : Nn (E (res (le_inf (inf_le_left.trans (LB.wchart_le L (fun k => gPt p ≫ ψ k) j k))
          (inf_le_right.trans (LB.wchart_le L (fun k => gPt p ≫ ψ k) j' k)) :
          LB.wchart L (fun k => gPt p ≫ ψ k) j ⊓ LB.wchart L (fun k => gPt p ≫ ψ k) j' ≤
            (gPt p ≫ ψ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
          (pullU (gPt p ≫ ψ k) _ (L.g (j k) (j' k))))) = 1 := by
        apply Units.ext
        have h1 := norm_unit (ψ k) (L.U (j k) ⊓ L.U (j' k))
          (fun w _ => ⟨hj k (x := w) trivial, hj' k (x := w) trivial⟩) (L.g (j k) (j' k))
        rw [← Category.id_comp (gPt p ≫ ψ k), GlobalTheory.Points.valR_comp] at h1
        exact (congrArg norm ((GlobalTheory.Points.valR_eq _ _ b _).symm.trans
          (GlobalTheory.Points.valR_res (U := (gPt p ≫ ψ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) _
          (le_inf (inf_le_left.trans (LB.wchart_le L (fun k => gPt p ≫ ψ k) j k))
          (inf_le_right.trans (LB.wchart_le L (fun k => gPt p ≫ ψ k) j' k))) b _))).trans h1
      exact (congrArg (· ^ ε k) this).trans (one_zpow _)
    have e2 : Nn (E (res inf_le_left (t.s j))) = Nn (E (res inf_le_right (t.s j'))) := by
      refine e.trans ?_
      refine (congrArg Nn (map_mul E _ _)).trans ((map_mul Nn _ _).trans ?_)
      exact (congrArg (· * _) hg).trans (one_mul _)
    have e3 := congrArg Units.val e2
    refine (congrArg norm ((GlobalTheory.Points.valR_eq _ _ b _).symm.trans
      (GlobalTheory.Points.valR_res _ inf_le_left b (t.s j).val))).symm.trans (Eq.trans e3 ?_)
    exact congrArg norm ((GlobalTheory.Points.valR_eq _ _ b _).symm.trans
      (GlobalTheory.Points.valR_res _ inf_le_right b (t.s j').val))
  · exact (GlobalTheory.Points.valR_eq _ _ a (t.s j).val).trans_ne ((t.s j).isUnit.map _).ne_zero

theorem exists_ext (u : ρ.UTest p y₀) (b : TF (R := u.V) (PadicAlgCl p) ⟶ u.D.toPre.P.A) :
    ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧ gPt p ≫ ψ = b.left := by
  have hp := u.D.toPre.P.isAb.proper
  have hv : ValuativeCriterion.Existence u.D.toPre.P.A.hom := by
    have : UniversallyClosed u.D.toPre.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at this
    exact this.1
  have w : b.left ≫ u.D.toPre.P.A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (OO p) (PadicAlgCl p))) ≫ spMap u.j := by
    refine (Over.w b).trans ?_
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hv { R := OO p, K := PadicAlgCl p, i₁ := b.left, i₂ := spMap u.j, commSq := ⟨w⟩ }
  exact ⟨l.l, l.fac_right, l.fac_left⟩

theorem exists_gtN (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)) : ∃ ν, u.GtN g ν := by
  obtain ⟨J₀, hJ₀, -⟩ := exists_intGood u
  refine ⟨fun χ => -Real.log ‖valF (𝟙 (Sp (PadicAlgCl p))) _
    ((g.s χ).s (fun k => J₀ (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖, fun J hJ χ => ?_⟩
  have h : ∀ k, ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧
      gPt p ≫ ψ = DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k := by
    intro k
    fin_cases k <;> exact exists_ext u _
  choose ψ h1 h2 using h
  have key : ∀ (φ : Fin 4 → (Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left)) (_ : ∀ k, gPt p ≫ ψ k = φ k)
      (t : LB.Gen (LB.LinComb u.D.toPre.P.L φ DegPre.gtε)), t.IsGen →
      ‖valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s (fun k => J (φ k))).val‖ =
        Real.exp (- -Real.log ‖valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s (fun k => J₀ (φ k))).val‖) := by
    intro φ hφ t ht
    obtain rfl : φ = fun k => gPt p ≫ ψ k := funext fun k => (hφ k).symm
    have A := norm_indep _ ψ _ t ht _ _ (fun k => hJ₀ _ (h1 k)) (fun k => hJ _ (h1 k))
    rw [neg_neg, Real.exp_log (norm_pos_iff.2 A.2)]
    exact A.1.symm
  exact key _ h2 (g.s χ) (g.isGen χ)
end GlobalTheory.ZH.GeoModel
end
