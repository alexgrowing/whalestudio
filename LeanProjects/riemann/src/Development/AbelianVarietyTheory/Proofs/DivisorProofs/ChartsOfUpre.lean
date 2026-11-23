import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VanishingIdealComapOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionCompIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem inv_apply_self {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) : inv f (f x) = x := by
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl

theorem chart_of_data {φ : InvFun (𝓞 E)} (Y : Model Xo c (RingHom.id c.F)) (BD' : EffCartierData Y.X) (d : ℕ)
    (x : gen Y) {k : Type} [Field k] {m e : ℕ} (ξ' : Sp (ChartRing k m e) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m e)))
    (P : PELUnif (maximalIdeal (ChartRing k m e)) t) (n : ℕ) (h : n = m) (s : Fin n → ChartRing k m e)
    (hs : ∀ i, s i = bdParam k m e (Fin.cast h i)) (δ : Fin n → LinearMap.BilinForm ℤ P.D.toPre.X) (a : Fin n → ℕ)
    (hx : ξ' (closedPoint _) = x) (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom)
    (hid : idlAlong (genBdIdeal Y) ξ' = Ideal.span {∏ i, s i})
    (hset : ∀ p : Sp (ChartRing k m e), ξ' p ∈ genBd Y ↔ ∏ i, s i ∈ p.asIdeal)
    (hsab : Nonempty (SABMap t Y.t (ξ' ≫ genι Y)))
    (hmono : IsMonomial P.D.toPre s (fun i => (l.M' : ℤ) • δ i))
    (hrank : Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q) (hcone : IsCone H.bar φ δ)
    (ha : ∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • δ i))
    (hBD : idlAlong BD'.idealSheaf (ξ' ≫ genι Y) = Ideal.span {∏ i, s i ^ a i})
    (hrig : GlobalTheory.RigChart.IsRigid P.D.toPre s (fun i => (l.M' : ℤ) • δ i)) :
    GlobalTheory.MumfordChart.HasChartOf φ Y BD' d x ∧ GlobalTheory.RigChart.HasRigidChart Y x := by
  subst h
  obtain rfl : s = bdParam k n e := funext fun i => by simpa using hs i
  have hmem : ∀ i, (l.M' : ℤ) • δ i ∈ levelForms H l.M' P.D.toPre.X := fun i =>
    (mem_levelForms_iff_smul (GlobalTheory.MumfordChart.level_ne_zero l)).2
      ⟨δ i, (balForms_eq_levelForms H P.D.toPre.X) ▸ hcone.mem i, rfl⟩
  let gam : Fin n → levelForms H l.M' P.D.toPre.X := fun i => ⟨(l.M' : ℤ) • δ i, hmem i⟩
  have hgam : ∀ i, (gam i : LinearMap.BilinForm ℤ P.D.toPre.X) = (l.M' : ℤ) • δ i := fun _ => rfl
  have hpb : IsPartOfBasis gam := hcone.isPartOfBasis_level (GlobalTheory.MumfordChart.level_ne_zero l) hgam
  exact ⟨⟨k, _, n, e, ξ', t, P, gam, δ, a, hx, het, hid, fun p => (hset p).trans Iff.rfl, hsab, hmono, hrank, hcone, hgam,
      ha, hBD⟩,
    ⟨k, _, n, e, ξ', t, P, gam, hx, het, hid, hset, hsab, hmono, hpb, hrig⟩⟩

end GlobalTheory.UChartOf

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem charts_of_upre {φ : InvFun (𝓞 E)} {S : Scheme.{0}} {j : Xo.XF c ⟶ S} [IsOpenImmersion j]
    {BD : EffCartierData S} {d : ℕ} (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S) (hj : Y.j ≫ ε.hom = j)
    (hsab : ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C →
      ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)))
    (hpre : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) (x : gen Y) (hx : x ∈ genBd Y) :
    GlobalTheory.MumfordChart.HasChartOf φ Y (BD.pull ε.hom (BD.keepsRegular_of_flat _)) d x ∧
      GlobalTheory.RigChart.HasRigidChart Y x := by
  let π : gen Y ⟶ S := genι Y ≫ ε.hom
  have hjQ : Y.jQ ≫ π = j := by
    simp only [π, ← Category.assoc]
    exact hj
  have hrange : ∀ w : gen Y, w ∈ Set.range Y.jQ ↔ π w ∈ Set.range j := by
    intro w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hjQ]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have : π (Y.jQ z) = π w := by rw [← hz, ← hjQ]; rfl
      rw [← inv_apply_self π (Y.jQ z), this, inv_apply_self]
  have hx' : π x ∉ Set.range j := fun h => hx ((hrange x).2 h)
  obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, hbd, hset, ha, hBD⟩ := hpre (π x) hx'
  obtain ⟨hm, hs, -, -, hrig, -, -⟩ := id htaut
  let ξ' : Sp (ChartRing k m e) ⟶ gen Y := ξ ≫ inv π
  have hξ : ξ' ≫ π = ξ := by simp [ξ']
  have hξg : ξ' ≫ genι Y = ξ ≫ ε.inv := by
    simp only [ξ', π, IsIso.inv_comp, IsIso.Iso.inv_hom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hvan : (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).comap π = genBdIdeal Y :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion (gen Y) S π _ (genBd Y) fun w =>
      (not_congr (hrange w)).trans Iff.rfl
  refine chart_of_data Y _ d x ξ' C.t C.P C.m hm C.s hs C.δ a ?_ ?_ ?_ ?_ ?_ C.mono C.rank C.cone ha ?_ hrig.1
  · change inv π (ξ (closedPoint _)) = x
    rw [hcl, inv_apply_self]
  · exact GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso ξ (inv π) het
  · rw [← hvan, GlobalTheory.TorRef.idlAlong_comap, hξ]
    exact hbd
  · intro p
    rw [mem_genBd, hrange, ← Scheme.Hom.comp_apply, hξ, hset p, not_not]
  · rw [hξg]
    exact hsab C htaut ξ hy
  · rw [EffCartierData.idealSheaf_pull, GlobalTheory.TorRef.idlAlong_comap, hξg, Category.assoc, ε.inv_hom_id,
      Category.comp_id]
    exact hBD

end GlobalTheory.UChartOf
