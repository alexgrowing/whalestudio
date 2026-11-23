import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PowEqOneOfIsFullLev
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsVtOverIsUUOverBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConnectionLinearInSection
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LBPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NullValue

section Val

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem isValueAt_congr {T : Over X} {s : LB.Sec (LPow A L a T)} {z z' : T ⟶ A} (e : z = z')
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))}
    {τ' : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z'.left) (fun _ => a))}
    (hτ : ∀ (j : Fin 1 → L.ι) (y : T.left), y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j →
      y ∈ LB.wchart L (fun _ : Fin 1 => z'.left) j → gm (𝟙 _) y _ (τ.s j) = gm (𝟙 _) y _ (τ'.s j))
    {v : Γ(T.left, ⊤)} (h : IsValueAt A L a s z τ v) : IsValueAt A L a s z' τ' v := by
  subst e
  have hU : ∀ j, (τ.s j).val = (τ'.s j).val := by
    intro j
    apply TopCat.Presheaf.section_ext T.left.sheaf
    intro y hy
    have hyU : (𝟙 T.left : T.left ⟶ T.left) y ∈ (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j := hy
    have key := hτ j y hy hy
    clear hτ h
    unfold gm at key
    rw [dif_pos hyU] at key
    have key2 := congrArg Units.val key
    simp only [MonoidHom.comp_apply] at key2
    unfold pullU at key2
    simp only [Units.coe_map, MonoidHom.coe_coe] at key2
    exact key2
  unfold IsValueAt at h ⊢
  intro j
  rw [← hU j]
  exact h j

private lemma gm_id_eq_germ_map {Y : Scheme.{0}} {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V)
    (x : Γ(Y, U)ˣ) :
    ((gm (𝟙 Y) y U x : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) =
      Y.presheaf.germ V y hy ((Y.presheaf.map (homOfLE hVU).op).hom (x : Γ(Y, U))) := by
  unfold gm
  rw [dif_pos (show (𝟙 Y : Y ⟶ Y) y ∈ U from hVU hy)]
  simp only [MonoidHom.comp_apply]
  unfold pullU
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [Y.presheaf.germ_res_apply]
  rfl

private lemma gm_id_eq_of_units_map_eq {Y : Scheme.{0}} {U₁ U₂ V : Y.Opens} (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) (x₁ : Γ(Y, U₁)ˣ)
    (x₂ : Γ(Y, U₂)ˣ) (y : Y) (hy : y ∈ V)
    (e : Units.map ((Y.presheaf.map (homOfLE h₁).op).hom : Γ(Y, U₁) →* Γ(Y, V)) x₁ =
      Units.map ((Y.presheaf.map (homOfLE h₂).op).hom : Γ(Y, U₂) →* Γ(Y, V)) x₂) :
    gm (𝟙 Y) y U₁ x₁ = gm (𝟙 Y) y U₂ x₂ := by
  apply Units.ext
  rw [gm_id_eq_germ_map h₁ y hy, gm_id_eq_germ_map h₂ y hy]
  have e2 := congrArg Units.val e
  simp only [Units.coe_map, MonoidHom.coe_coe] at e2
  rw [e2]

theorem isValueAt_one_pull (ρ : LB.Gen (L.pull (eSec A))) {T T' : Over X} (g : T' ⟶ T)
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (hs : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) s s') {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s 1 (rigT A L ρ T a) v) :
    IsValueAt A L a s' 1 (rigT A L ρ T' a) (g.left.appTop.hom v) := by
  have h1 := Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isValueAt_pull A L a g 1 hs hv
  have hc := Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.corr_rigT_pull A L ρ g a
  have e : g ≫ (1 : T ⟶ A) = 1 := by simp
  refine isValueAt_congr A L a e ?_ h1
  intro j y hy hy'
  unfold LB.Gen.Corr at hc
  have key := hc j j (fun k₁ k₂ _ => by rw [Subsingleton.elim k₁ k₂])
    (fun k₁ k₂ _ => by rw [Subsingleton.elim k₁ k₂]) (fun k k' _ => by rw [Subsingleton.elim k k'])
  unfold res at key
  refine gm_id_eq_of_units_map_eq _ _ _ _ y ?_ key
  exact ⟨hy, hy'⟩

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem baseChange {N : ℕ} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap ψ y z)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G) (hp : p'.left = spMap ψ.toRingHom ≫ p.left)
    {w : S} (hw : IsNullVal Xo c N y p w) : IsNullVal Xo c N z p' (ψ w) := by
  obtain ⟨F, hVt, hV⟩ := hw
  have hx : spMap ψ.toRingHom ≫ y.x = z.x := by
    unfold FrMap at hm
    exact hm.1.symm
  let g : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx
  have hg : g.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm g hg
  have hF := GlobalTheory.VVRank.isPullSec_pullS (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) ((N : ℤ) ^ 2) g F
  have hpg : p' = g ≫ p := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hg]
    exact hp
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  unfold IsNullVal
  refine ⟨GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) g F, ?_, ?_⟩
  · unfold IsVtOver at hVt ⊢
    obtain ⟨t', α₀, α, s₁, U, ht', hok, g₀, hnm, cα, tw, hsym, hact⟩ := hVt
    have hok' : t' = p := hok
    obtain ⟨α', cα', tw'⟩ := GlobalTheory.VtBaseChange.exists_mulTwist Xo.univ.t.G hL N g hs g₀ cα tw
    obtain ⟨θ', -, -, hsymP, hactP⟩ :=
      GlobalTheory.ThetaPullback.exists_thetaGrp_pullback _ Xo.univ.t.G Xo.univ.t.PP.L hL ((N : ℤ) ^ 2) _ _ g U
    refine ⟨g ≫ t', α₀, α', _, θ', ?_, ?_, g₀, hnm, cα', tw', hsymP _ _ hsym,
      hactP _ _ _ _ hact (GlobalTheory.VVRank.isPullSec_pullS (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) _ g s₁) hF⟩
    · rw [hpg, hok']
    · show g ≫ t' = p'
      rw [hpg, hok']
  · have h1 := isValueAt_one_pull Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Xo.univ.t.PP.rig g hF hV
    have e2 : g.left.appTop.hom (toΓ S w) = toΓ T (ψ w) := GlobalTheory.NabLinear.appTop_toΓ ψ.toRingHom w
    rw [e2] at h1
    exact h1

open GlobalTheory.ThetaValueWeight in

theorem triangular {N : ℕ} {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} {t : Ix Dw → Sˣ}
    (hb : FrBor t y y') (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G) (hp : p'.left = p.left)
    {w : S} (hw : IsNullVal Xo c N y p w) : IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  have hxx : y'.x = y.x := by
    unfold FrBor at hb
    exact hb.1
  obtain ⟨d, rfl⟩ := GlobalTheory.ThetaValueWeight.exists_reframe y y' hxx
  have hpp : p' = p := Over.OverMorphism.ext hp
  subst hpp
  obtain ⟨F, hVt, hV⟩ := hw
  have hgen := fun i => GlobalTheory.ThetaValueWeight.gen_eq d hb i
  unfold IsNullVal
  refine ⟨scaleSec Xo.univ.t.G (toΓ S (t none : S)) F, ?_, ?_⟩
  · exact isVtOver_scale Xo.univ.t.G Xo.univ.t.PP (T := ptO Xo y.x) (s := y.s) (s₀ := d.s)
      (toΓ S (t none : S)) (fun j => hgen j) hVt
  · have h1 := GlobalTheory.NabLinear.isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (𝟙 (ptO Xo y.x))
      (F := F) (F' := scaleSec Xo.univ.t.G (toΓ S (t none : S)) F) (r := toΓ S (t none : S)) (fun _ => rfl)
      (isPullSec_id Xo.univ.t.G F) (isPullSec_id Xo.univ.t.G _) hV
    convert h1 using 1
    rw [map_mul]
    rfl

end GlobalTheory.NullValue

namespace GlobalTheory

theorem nullValue_existsUnique_natural_linear : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (N : ℕ), Odd N → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (p : ptO Xo y.x ⟶ Xo.univ.t.G), p ^ (N ^ 2) = 1 → ∃! w, IsNullVal Xo c N y p w) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap ψ y z → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G), p'.left = spMap ψ.toRingHom ≫ p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N z p' (ψ w)) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G), p'.left = p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  intro hL E _ _ _ H Dw l Xo c N hN
  refine ⟨?_, ?_, ?_⟩
  · intro S _ _ y p hp
    obtain ⟨w, hw⟩ := GlobalTheory.EtaForm.Model.exists_isNullVal Xo c hL hN y p hp
    exact ⟨w, hw, fun w' hw' => GlobalTheory.EtaForm.Model.isNullVal_unique Xo c hL hN y p hp hw' hw⟩
  · intro S T _ _ _ _ ψ y z hm p p' hp w hw
    exact NullValue.baseChange ψ hm p p' hp hw
  · intro S _ _ y y' t hb p p' hp w hw
    exact NullValue.triangular hb p p' hp hw

end GlobalTheory
