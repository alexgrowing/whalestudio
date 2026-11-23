import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAlgebraEqZeroOfVanishOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartVanishingSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitOfNonvanishingPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleFromUnitRatiosStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartUnitSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OverlappingAnalyticChartsRatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genV_res {N N' : X.Opens} (l : N' ≤ N) (h' : genPt ξ ∈ N') (h : genPt ξ ∈ N) (v : Γ(X, N)) :
    genV ξ N' h' (X.presheaf.map (homOfLE l).op v) = genV ξ N h v := by
  have e : X.presheaf.germ N' (genPt ξ) h' (X.presheaf.map (homOfLE l).op v) = X.presheaf.germ N (genPt ξ) h v :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom e

theorem unitAt_genV {N : X.Opens} {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) (h : genPt ξ ∈ N) {v : Γ(X, N)}
    (hv : IsUnit v) : unitAt ξ ⟨q, hq⟩ (genV ξ N h v) := by
  obtain ⟨u, rfl⟩ := hv
  have e : genV ξ N h u * genV ξ N h (u⁻¹ : Γ(X, N)ˣ) = 1 := by rw [← map_mul]; simp
  refine ⟨left_ne_zero_of_mul_eq_one e, ⟨_, genMap_germ N hq hN h _⟩, ?_⟩
  rw [inv_eq_of_mul_eq_one_right e]
  exact ⟨_, genMap_germ N hq hN h _⟩

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem gaga_rat_C : GagaSections → ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] [Algebra ℂ Ω] (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ), IsProper s → Smooth s → ξ ≫ s = spMap (algebraMap ℂ Ω) → IsCptGen ξ → ConstClosed ℂ Ω → L.IsVB 1 ⊤ → genPt ξ ∈ W → (∀ p : Cpt ξ, p.1 ∈ W → L.IsGenAt p 1) → (∀ (x : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre x), x ≫ s = spMap (RingHom.id ℂ) → ∃ t : Ω, L.IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s (RingHom.id ℂ) ξ W F t x) → ∃ (f : Ω) (κ : ℂ), κ ≠ 0 ∧ (∀ p : Cpt ξ, L.IsGenAt p f) ∧ ∀ y : Sp ℂ ⟶ X, y ≫ s = spMap (RingHom.id ℂ) → ⊤ ≤ y ⁻¹ᵁ W → genPt ξ ⤳ centre y → ValAt ξ y f (κ * F y) := by
  have dens := GlobalTheory.T.smooth_algebra_eq_zero_of_vanish_open
  have chart := GlobalTheory.T.analytic_chart_vanishing_section
  have unit := GlobalTheory.T.is_unit_of_nonvanishing_points
  have trans := GlobalTheory.T.line_bundle_from_unit_ratios
  have hch := GlobalTheory.T.analytic_chart_unit_section
  have cmp := GlobalTheory.T.overlapping_analytic_charts_ratio
  intro hG X s Ω _ _ ξ L W F hp hs hξs hgen hcl hVB hW h1 hext
  haveI : Smooth s := hs
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨Z, hZ, hZc, -⟩ := cpt_open_integral X Ω ξ hgen
  have spid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by simp
  choose Uo hUo b hb hfr using fun p : Cpt ξ => hVB p trivial
  let Uc : Cpt ξ → X.Opens := fun p => Uo p ⊓ Z
  let T : Cpt ξ → Ω := fun p => b p 0
  have inZ : ∀ p q, q ∈ Uc p → genPt ξ ⤳ q := fun p q hq => (hZ q).1 hq.2
  have memU : ∀ p : Cpt ξ, p.1 ∈ Uc p := fun p => ⟨hUo p, (hZ _).2 p.2⟩
  have gen : ∀ (p q : Cpt ξ), q.1 ∈ Uc p → L.IsGenAt q (T p) := fun p q hq => by
    obtain ⟨li, sp⟩ := hfr p q trivial hq.1
    refine ⟨li.ne_zero 0, ?_⟩
    rw [sp]
    congr 1
    ext e
    simp [T, Fin.exists_fin_one, eq_comm]
  have hunitW : ∀ (p : Cpt ξ) (q : X) (hq : genPt ξ ⤳ q), q ∈ Uc p → q ∈ W → unitAt ξ ⟨q, hq⟩ (T p) := fun p q hq a c => by
    have := unitAt_div_of_isGenAt (h1 ⟨q, hq⟩ c) (gen p ⟨q, hq⟩ a)
    simpa using this
  let V : Option (Cpt ξ) → X.Opens := fun o => o.elim ⟨(Z : Set X)ᶜ, hZc.isOpen_compl⟩ Uc
  have hV1 : ∀ i, ∀ q ∈ V (some i), genPt ξ ⤳ q := fun i q hq => inZ i q hq
  have hV2 : ∀ q ∈ V none, ¬ genPt ξ ⤳ q := fun q hq h => hq ((hZ q).2 h)
  have hV3 : ∀ (i j : Cpt ξ) (q : X) (hq : genPt ξ ⤳ q), q ∈ V (some i) → q ∈ V (some j) →
      unitAt ξ ⟨q, hq⟩ (T j / T i) := fun i j q hq a c =>
    unitAt_div_of_isGenAt (gen i ⟨q, hq⟩ a) (gen j ⟨q, hq⟩ c)
  have hV4 : ⨆ i, V i = ⊤ := by
    refine top_le_iff.1 fun q _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases h : q ∈ Z
    · exact ⟨some ⟨q, (hZ q).1 h⟩, memU ⟨q, (hZ q).1 h⟩⟩
    · exact ⟨none, h⟩
  obtain ⟨g, hLB, hg⟩ := trans X Ω ξ (Cpt ξ) V T hgen hV1 hV2 hV3 hV4
  let Rel : Cpt ξ → (Sp ℂ ⟶ X) → ℂ → Prop := fun p x c => ∃ (d : ℕ) (B : Set (Fin d → ℂ))
    (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) (b₁ : Fin d → ℂ),
    HChart s ξ W (Uc p) F (T p) B Y H ∧ b₁ ∈ B ∧ Y b₁ = x ∧ H b₁ = c
  have relEx : ∀ (p : Cpt ξ) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → centre x ∈ Uc p → ∃ c, Rel p x c := by
    intro p x hx hm
    have hc : genPt ξ ⤳ centre x := inZ p _ hm
    obtain ⟨t, ht, he⟩ := hext x hc (by rw [hx, spid])
    have u := unitAt_div_of_isGenAt (gen p ⟨centre x, hc⟩ hm) ht
    obtain ⟨N, hN, v, lN, uv, ev⟩ := exists_unit_section hgen hc u (Uc p) hm
    obtain ⟨d, B, Y, b₁, hC, hb₁, e₁, hin, hd⟩ := chart dens X s Ω ξ W N x hs hgen hW hx hc hN
    have gm : ∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N),
        genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T p := fun q hq h => by
      rw [genMap_germ N hq h (genPt_mem hc hN), ← genMap_germ N hc hN (genPt_mem hc hN), ev]
    subst e₁
    obtain ⟨B₂, H, m₂, hH⟩ := hch X s Ω ξ W (Uc p) N F (T p) t v d B Y b₁ hgen hC hb₁ hin lN hd uv gm
      (gen p p (memU p)).1 he
    exact ⟨_, d, B₂, Y, H, b₁, hH, m₂, rfl, rfl⟩
  have relCmp : ∀ (p p' : Cpt ξ) (x : Sp ℂ ⟶ X) (c c' r : ℂ), Rel p x c → Rel p' x c' →
      ValAt ξ x (T p' / T p) r → c = r * c' := by
    rintro p p' x c c' r ⟨d, B, Y, H, b₁, hH, m₁, rfl, rfl⟩ ⟨d', B', Y', H', b₂, hH', m₂, e, rfl⟩ hr
    exact cmp X s Ω ξ W (Uc p) (Uc p') F (T p) (T p') d d' B B' Y Y' H H' b₁ b₂ r hgen hH hH'
      (hunitW p) (hunitW p') m₁ m₂ e.symm hr
  have relU : ∀ (p : Cpt ξ) (x : Sp ℂ ⟶ X) (c c' : ℂ), Rel p x c → Rel p x c' → c = c' := fun p x c c' a a' => by
    have hz : genPt ξ ⤳ centre x := by
      obtain ⟨d, B, Y, H, b₁, hH, m₁, rfl, -⟩ := a
      exact hH.cpt b₁ m₁
    have := relCmp p p x c c' 1 a a' (by
      rw [div_self (gen p p (memU p)).1]; exact ValAt.one hz)
    simpa using this
  classical
  let h0 : Cpt ξ → (Sp ℂ ⟶ X) → ℂ := fun p x => if hh : ∃ c, Rel p x c then hh.choose else 0
  have h0s : ∀ p x c, Rel p x c → h0 p x = c := fun p x c hc => by
    have hh : ∃ c, Rel p x c := ⟨c, hc⟩
    simp only [h0, dif_pos hh]
    exact relU p x _ _ hh.choose_spec hc
  let h : Option (Cpt ξ) → (Sp ℂ ⟶ X) → ℂ := fun o => o.elim (fun _ => 0) h0
  let LL : LB X := LB.mk (Option (Cpt ξ)) V g
  have hhol : ∀ (i : LL.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y →
      (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ LL.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B := by
    rintro (_ | p) m B y oB hy hb
    · exact differentiableOn_const _
    · intro b₀ h₀
      obtain ⟨c, hc⟩ := relEx p (y b₀) (hb b₀ h₀).1 ((top_le_iff_centre _ _).1 (hb b₀ h₀).2)
      obtain ⟨d, B₁, Y, H, b₁, hH, m₁, e, -⟩ := hc
      obtain ⟨ε, κ, ε0, sub, dκ, k₀, hκ⟩ := hH.chart.factor m B y oB hy (fun b hb' => (hb b hb').1) b₀ h₀ b₁ m₁ e.symm
      have eq : ∀ b ∈ ball b₀ ε, h (some p) (y b) = H (κ b) := fun b hb' => by
        obtain ⟨k1, k2⟩ := hκ b hb'
        exact h0s p _ _ ⟨d, B₁, Y, H, κ b, hH, k1, k2.symm, rfl⟩
      have m₁' : κ b₀ ∈ B₁ := k₀ ▸ m₁
      have dH : DifferentiableAt ℂ H (κ b₀) := (hH.hol _ m₁').differentiableAt (hH.chart.isOpen.mem_nhds m₁')
      have dk : DifferentiableAt ℂ κ b₀ := dκ.differentiableAt (ball_mem_nhds _ ε0)
      refine (DifferentiableAt.congr_of_eventuallyEq (dH.comp b₀ dk) ?_).differentiableWithinAt
      filter_upwards [ball_mem_nhds b₀ ε0] with b hb'
      exact eq b hb'
  have hcomp : ∀ (i j : LL.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (LL.U i ⊓ LL.U j) →
      h i x = valAt' x (LL.U i ⊓ LL.U j) (LL.g i j).val * h j x := by
    rintro (_ | p) (_ | p') x hx hm
    · simp [h]
    · have m := (top_le_iff_centre _ _).1 hm
      exact absurd (inZ p' _ m.2) (hV2 _ m.1)
    · have m := (top_le_iff_centre _ _).1 hm
      exact absurd (inZ p _ m.1) (hV2 _ m.2)
    · have m := (top_le_iff_centre _ _).1 hm
      obtain ⟨c, hc⟩ := relEx p x hx m.1
      obtain ⟨c', hc'⟩ := relEx p' x hx m.2
      have hz := inZ p _ m.1
      have vr := ValAt.of_section m hz (hg p p' _ hz m)
      show h0 p x = _ * h0 p' x
      rw [h0s _ _ _ hc, h0s _ _ _ hc']
      exact relCmp p p' x c c' _ hc hc' vr
  obtain ⟨σ, hσ⟩ := hG X s hp hs LL hLB h hhol hcomp
  have hne : ∀ (p : Cpt ξ) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → centre x ∈ Uc p → h0 p x ≠ 0 := fun p x hx hm => by
    obtain ⟨c, hc⟩ := relEx p x hx hm
    rw [h0s _ _ _ hc]
    obtain ⟨d, B, Y, H, b₁, hH, m₁, -, rfl⟩ := hc
    exact hH.ne b₁ m₁
  have hu : ∀ p, IsUnit (σ.f (some p)) := fun p => unit X s (Uc p) _ inferInstance fun x hx hm => by
    rw [show valAt' x (Uc p) (σ.f (some p)) = h0 p x from hσ (some p) x hx ((top_le_iff_centre _ _).2 hm)]
    exact hne p x hx hm
  have gU : ∀ p : Cpt ξ, genPt ξ ∈ Uc p := fun p => genPt_mem p.2 (memU p)
  let c : Cpt ξ → Ω := fun p => genV ξ (Uc p) (gU p) (σ.f (some p))
  have hcT : ∀ p p', c p * T p = c p' * T p' := fun p p' => by
    have gI : genPt ξ ∈ Uc p ⊓ Uc p' := ⟨gU p, gU p'⟩
    have e := (congrArg (genV ξ (Uc p ⊓ Uc p') gI) (σ.compat (some p) (some p'))).trans
      (map_mul (genV ξ (Uc p ⊓ Uc p') gI) _ _)
    have e₁ := genV_res (ξ := ξ) (inf_le_left : Uc p ⊓ Uc p' ≤ Uc p) gI (gU p) (σ.f (some p))
    have e₂ := genV_res (ξ := ξ) (inf_le_right : Uc p ⊓ Uc p' ≤ Uc p') gI (gU p') (σ.f (some p'))
    have e₃ := (genMap_germ (ξ := ξ) (Uc p ⊓ Uc p') specializes_rfl gI gI (g (some p) (some p')).val).symm.trans
      (hg p p' _ specializes_rfl gI)
    have e₄ : c p = T p' / T p * c p' := by
      show genV ξ (Uc p) (gU p) (σ.f (some p)) = _ * genV ξ (Uc p') (gU p') (σ.f (some p'))
      rw [← e₁, ← e₂, ← e₃]
      exact e
    have n₁ := (gen p p (memU p)).1
    rw [e₄]
    field_simp
  let f : Ω := c ⟨genPt ξ, specializes_rfl⟩ * T ⟨genPt ξ, specializes_rfl⟩
  have hf : ∀ p, f = c p * T p := fun p => hcT _ p
  refine ⟨f, 1, one_ne_zero, fun p => ?_, fun y hy hWy hc => ?_⟩
  · rw [hf p]
    exact isGenAt_mul_of_unitAt (gen p p (memU p)) (unitAt_genV p.2 (memU p) (gU p) (hu p))
  · let p : Cpt ξ := ⟨centre y, hc⟩
    have mU : centre y ∈ Uc p := memU p
    have hyW : centre y ∈ W := (top_le_iff_centre _ _).1 hWy
    have hy' : y ≫ s = 𝟙 _ := by rw [hy, spid]
    obtain ⟨r, -, hr⟩ := ValAt.exists_ne_zero hgen hc (hunitW p _ hc mU hyW)
    have v1 : ValAt ξ y (c p) (valAt' y (Uc p) (σ.f (some p))) :=
      ValAt.of_section mU hc (genMap_germ _ hc mU (gU p) _)
    have v2 := ValAt.mul v1 hr
    rw [show valAt' y (Uc p) (σ.f (some p)) = h0 p y from hσ (some p) y hy' ((top_le_iff_centre _ _).2 mU)] at v2
    obtain ⟨cc, hcc⟩ := relEx p y hy' mU
    have e : F y = h0 p y * r := by
      rw [h0s _ _ _ hcc]
      obtain ⟨d, B, Y, H, b₁, hH, m₁, rfl, rfl⟩ := hcc
      exact hH.rel b₁ m₁ hyW r hr
    rw [_root_.one_mul, e, hf p]
    exact v2

end GlobalTheory.CompanionTheory.Ar.Flat
