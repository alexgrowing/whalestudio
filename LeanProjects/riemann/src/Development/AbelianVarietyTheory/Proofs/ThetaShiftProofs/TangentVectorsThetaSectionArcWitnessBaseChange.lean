import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescentPowerIsoEndomorphismAbelianPartUniformiza

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcBaseChange

section Square

variable {B B' B₀ B₀' : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {M₀' : LB B₀'}
  {φ : B ⟶ B₀} {φ' : B' ⟶ B₀'} {Φ : B' ⟶ B} {π : B₀' ⟶ B₀}

def Sq (w : LB.Iso M (M₀.pull φ)) (wD : LB.Iso M' (M.pull Φ)) (wp : LB.Iso M₀' (M₀.pull π))
    (w' : LB.Iso M' (M₀'.pull φ')) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ B') (z : Z) (j : M₀.ι) (i : M.ι) (i' : M₀'.ι) (k : M'.ι), φ (Φ (r z)) ∈ M₀.U j →
    Φ (r z) ∈ M.U i → φ' (r z) ∈ M₀'.U i' → r z ∈ M'.U k →
    gw w (r ≫ Φ) z j i * gw wD r z i k = gw wp (r ≫ φ') z j i' * gw w' r z i' k

variable {w : LB.Iso M (M₀.pull φ)} {wD : LB.Iso M' (M.pull Φ)} {wp : LB.Iso M₀' (M₀.pull π)}
  {w' : LB.Iso M' (M₀'.pull φ')}

theorem sq_of_tri (hs : φ' ≫ π = Φ ≫ φ) {w₁ : LB.Iso M' (M₀.pull (Φ ≫ φ))} {w₂ : LB.Iso M' (M₀.pull (φ' ≫ π))}
    (e : HEq w₁ w₂) (T₁ : Tri w wD w₁) (T₂ : Tri wp w' w₂) : Sq w wD wp w' := by
  intro Z r z j i i' k hj hi hi' hk
  have hj' : π (φ' (r z)) ∈ M₀.U j := (congrArg (fun g => g (r z) ∈ M₀.U j) hs).mpr hj
  rw [← T₁ Z r z j i k hj hi hk, ← T₂ Z r z j i' k hj' hi' hk]
  exact gw_heq hs.symm e r z j k

theorem genRelR_baseChange (hs : φ' ≫ π = Φ ≫ φ) (S : Sq w wD wp w') (hw : w.IsGen) (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {K : Type} [Fintype K] {ε : K → ℤ} {T T' N N' : Scheme.{0}} {o : K → (T ⟶ B)} {o' : K → (T' ⟶ B')}
    {g : K → (N ⟶ B₀)} {g' : K → (N' ⟶ B₀')} {t : LB.Gen (LB.LinComb M o ε)} {t' : LB.Gen (LB.LinComb M' o' ε)}
    {ν : LB.Gen (LB.LinComb M₀ g ε)} {ν' : LB.Gen (LB.LinComb M₀' g' ε)} (ht : t.IsGen) (hν : ν.IsGen)
    {h : T' ⟶ T} {d : N' ⟶ N} (ho : ∀ k, o' k ≫ Φ = h ≫ o k)
    (Ht : PMaps wD o' o ε t' t h) (Hν : PMaps wp g' g ε ν' ν d)
    {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A'] {q : Sp A' ⟶ Sp A}
    {v : Sp A ⟶ T} {v' : Sp A' ⟶ T'} {κ : Sp A ⟶ N} {κ' : Sp A' ⟶ N'} (hv : v' ≫ h = q ≫ v) (hκ : κ' ≫ d = q ≫ κ)
    (hp : ∀ k, (v' ≫ o' k) ≫ φ' = κ' ≫ g' k)
    (H : GenRelR w (LB.pullGen _ _ _ t v) (LB.pullGen _ _ _ ν κ)) :
    GenRelR w' (LB.pullGen _ _ _ t' v') (LB.pullGen _ _ _ ν' κ') := by
  have P := ConstGrp.pmaps_of_genRelR ((isGen_iff w).1 hw) hM hM₀ (DVR.pullGen_isGen _ _ _ _ ht v)
    (DVR.pullGen_isGen _ _ _ _ hν κ) H
  refine (genRelR_iff w' _ _).2 ⟨hp, fun j j₀ h₀ h₁ => congrArg Units.val ?_⟩
  set z := cpt A'
  choose i hi using fun k => exists_chart hM (Φ ((v' ≫ o' k) z))
  choose p hp' using fun k => exists_chart hM₀ (φ (Φ ((v' ≫ o' k) z)))
  have c₁ : ∀ k, (v' ≫ o' k) ≫ Φ = q ≫ v ≫ o k := fun k => by
    rw [Category.assoc, ho, ← Category.assoc, hv, Category.assoc]
  have c₂ : ∀ k, (v ≫ o k) (q z) = Φ ((v' ≫ o' k) z) := fun k => congrArg (fun f => f z) (c₁ k).symm
  have c₃ : ∀ k, g' k (κ' z) = φ' ((v' ≫ o' k) z) := fun k => congrArg (fun f => f z) (hp k).symm
  have c₄ : ∀ y, π (φ' y) = φ (Φ y) := fun y => congrArg (fun f => f y) hs
  have e₁ := Hν _ κ' z p j₀ (fun k => by rw [c₃, c₄]; exact hp' k) (fun k => by rw [c₃]; exact h₀ k)
  have e₂ := P _ q z p i (fun k => by rw [c₂]; exact hp' k) (fun k => by rw [c₂]; exact hi k)
  have e₃ := Ht _ v' z i j hi h₁
  rw [Category.comp_id, gm_pullGen', gm_pullGen', ← hκ, e₁, ← hv, e₃, ← _root_.mul_assoc,
    ← Finset.prod_mul_distrib] at e₂
  have e₄ : ∀ k, gw w (q ≫ v ≫ o k) z (p k) (i k) ^ ε k * gw wD (v' ≫ o' k) z (i k) (j k) ^ ε k =
      gw wp (κ' ≫ g' k) z (p k) (j₀ k) ^ ε k * gw w' (v' ≫ o' k) z (j₀ k) (j k) ^ ε k := fun k => by
    rw [← mul_zpow, ← mul_zpow, ← c₁, ← hp, S _ (v' ≫ o' k) z _ _ _ _ (hp' k) (hi k) (h₀ k) (h₁ k)]
  rw [Finset.prod_congr rfl fun k _ => e₄ k, Finset.prod_mul_distrib, _root_.mul_assoc] at e₂
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp]
  exact (mul_left_cancel e₂).symm

theorem comp_eq_of_squares {T T' N N' Z Z' : Scheme.{0}} (hs : φ' ≫ π = Φ ≫ φ) {o : T ⟶ B} {o' : T' ⟶ B'}
    {g : N ⟶ B₀} {g' : N' ⟶ B₀'} {h : T' ⟶ T} {d : N' ⟶ N} (ho : o' ≫ Φ = h ≫ o) (hg : g' ≫ π = d ≫ g)
    {q : Z' ⟶ Z} {v : Z ⟶ T} {v' : Z' ⟶ T'} {κ : Z ⟶ N} {κ' : Z' ⟶ N'} (hv : v' ≫ h = q ≫ v) (hκ : κ' ≫ d = q ≫ κ)
    (H : (v ≫ o) ≫ φ = κ ≫ g) : ((v' ≫ o') ≫ φ') ≫ π = (κ' ≫ g') ≫ π := by
  rw [Category.assoc] at H
  simp only [Category.assoc]
  rw [hs, reassoc_of% ho, reassoc_of% hv, H, hg, reassoc_of% hκ]

end Square

section Sections

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

def SRel (w : LB.Iso L' (L.pull F)) (s : L.Sec) (s' : L'.Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
    gs (r ≫ F) z (L.U j) (s.f j) = (gw w r z j k).val * gs r z (L'.U k) (s'.f k)

theorem srel_of {w : LB.Iso L' (L.pull F)} {s : L.Sec} {s' : L'.Sec} {s₂ : (L.pull F).Sec} (h₁ : PullSec F s s₂)
    (h₂ : IsoMaps w s' s₂) : SRel w s s' := by
  intro Z r z j k hj hk
  have hm : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun _ hx => mem_pull.1 hx
  have e := congrArg (gs r z _) (h₂ (fun _ => j) k)
  rw [gs_res r z _ hm, gs_mul r z _ hm, gs_res r z _ hm, h₁ (fun _ => j) le] at e
  exact (gs_appLE F _ _ le r z hm.1 _).symm.trans (e.trans (congrArg (· * _) (gs_unit r z _ hm _)))

theorem gs_h0Sec {σ : Out.H0 L 1} {θ : L.Sec} (h : SectionOfLineBundleOne σ θ) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (p : Fin 1 → L.ι)
    (hp : r z ∈ L.U (p 0)) :
    gs r z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) p) (σ.f p) = gs r z (L.U (p 0)) (θ.f (p 0)) := by
  have le : LB.wchart L (fun _ : Fin 1 => 𝟙 X) p ≤ L.U (p 0) := fun y hy => Set.mem_iInter.1 hy 0
  rw [h p le]
  exact gs_res r z le (Set.mem_iInter.2 fun k => by rw [Subsingleton.elim k 0]; exact hp) _

theorem exists_h0Sec (θ : L.Sec) : ∃ σ : Out.H0 L 1, SectionOfLineBundleOne σ θ := by
  obtain ⟨t, ht⟩ := ThetaUnit.exists_powerSection_of_chartFunctions θ
  refine ⟨t, fun j h => fn_ext fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  have hy' : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) := hy
  exact (ht _ (𝟙 X) y k (h hy')).trans (gs_res (𝟙 X) y h hy' _).symm

theorem srel_of_rig {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (hs : Function.Surjective G'.hom.appTop.hom) {L₁ L₂ : RigLB G} {L₁' L₂' : RigLB G'}
    (hL : L₁ = L₂) (hL' : L₁' = L₂') {Ψ₁ Ψ₂ : G'.left ⟶ G.left} (hΨ : Ψ₂ = Ψ₁) {e₁ e₂} (he : e₂ = e₁)
    {h₁ : eSec G' ≫ Ψ₁ = e₁ ≫ eSec G} {h₂ : eSec G' ≫ Ψ₂ = e₂ ≫ eSec G}
    {w₁ : LB.Iso L₁'.L (L₁.L.pull Ψ₁)} {w₂ : LB.Iso L₂'.L (L₂.L.pull Ψ₂)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen)
    (m₁ : LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L₁'.rig
      (rigPullOf Ψ₁ e₁ h₁ L₁.L L₁.rig))
    (m₂ : LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L₂'.rig
      (rigPullOf Ψ₂ e₂ h₂ L₂.L L₂.rig))
    {θ₁ : L₁.L.Sec} {θ₂ : L₂.L.Sec} (hθ : HEq θ₂ θ₁) {θ₂' : L₂'.L.Sec} (H : SRel w₂ θ₂ θ₂') :
    ∃ θ₁' : L₁'.L.Sec, HEq θ₂' θ₁' ∧ SRel w₁ θ₁ θ₁' := by
  subst hL hL' hΨ he
  cases hθ
  obtain rfl : w₁ = w₂ := iso_eq_of_maps_along_section (S := S') (exists_chart L₁'.isLB)
    (fun y => (exists_chart L₁.isLB (Ψ₂ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    G'.hom (eSec G') (Over.w _) hs g₁ g₂ m₁ m₂
  exact ⟨θ₂', HEq.rfl, H⟩

end Sections

section Term

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : Out.DegPre R} {D' : Out.DegPre R'}
  {B₀ B₀' : Scheme.{0}} {M₀ : LB B₀} {M₀' : LB B₀'} {φ : D.P.A.left ⟶ B₀} {φ' : D'.P.A.left ⟶ B₀'}
  {Φ : D'.P.A.left ⟶ D.P.A.left} {π : B₀' ⟶ B₀} {w : LB.Iso D.P.L (M₀.pull φ)} {wD : LB.Iso D'.P.L (D.P.L.pull Φ)}
  {wp : LB.Iso M₀' (M₀.pull π)} {w' : LB.Iso D'.P.L (M₀'.pull φ')} {th : M₀.Sec} {th' : M₀'.Sec}

theorem val_of_isPullTerm {t : D.SecB 1 0} (h : ThetaUnit.IsPullTerm D φ w th t) {Z : Scheme.{0}}
    (r : Z ⟶ D.P.A.left) (z : Z) {J} (hJ : Good D.P.L z J) (j₀ : M₀.ι) (hy : φ (r z) ∈ M₀.U j₀) :
    gs (r ≫ φ) z _ (th.f j₀) = (gw w r z j₀ (J r)).val * sval t r z J := by
  have e₁ : r ≫ D.famφB 0 1 = r := by rw [ThetaUnit.famφB_zero_one, Category.comp_id]
  let j : Fin 4 → D.P.L.ι := fun k => J (r ≫ D.famφB 0 k)
  have hj : j 1 = J r := congrArg J e₁
  let V := LB.wchart D.P.L (D.famφB 0) j ⊓ ((M₀.pull φ).U (fun _ => j₀) ⊓ D.P.L.U (j 1))
  have hm : r z ∈ V := ⟨hJ.mem _ r, mem_pull.2 hy, hj ▸ hJ r⟩
  have h₃ : V ≤ φ ⁻¹ᵁ M₀.U j₀ := fun z hz => mem_pull.1 hz.2.1
  have e := congrArg (gs r z V) (h j j₀ V inf_le_left inf_le_right h₃ fun k k' e => congrArg (fun q => J (r ≫ q)) e)
  refine (gs_appLE φ _ _ h₃ r z hm _).symm.trans (e.trans ((gs_mul r z V hm _ _).trans ?_))
  refine (congrArg₂ (· * ·) ((gs_res r z inf_le_right hm _).trans (gs_unit r z _ hm.2 _))
    (gs_res r z inf_le_left hm _)).trans ?_
  rw [← hj]
  rfl

theorem isPullTerm_baseChange (hs : φ' ≫ π = Φ ≫ φ) (S : Sq w wD wp w') (hM₀ : M₀.IsLB) (hth : SRel wp th th')
    (hc : ∀ κ, D'.famφB 0 κ ≫ Φ = Φ ≫ D.famφB 0 κ) {t : D.SecB 1 0} {t' : D'.SecB 1 0}
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
      (∀ κ, Φ (D'.famφB 0 κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, D'.famφB 0 κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Φ) z (LB.wchart D.P.L (D.famφB 0) p) (t.f p) =
        (∏ κ, gw wD (r ≫ D'.famφB 0 κ) z (p κ) (q κ) ^ Out.DegPre.famε 1 κ).val *
          gs r z (LB.wchart D'.P.L (D'.famφB 0) q) (t'.f q))
    (h : ThetaUnit.IsPullTerm D φ w th t) : ThetaUnit.IsPullTerm D' φ' w' th' t' := by
  refine ThetaUnit.isPullTerm_iff.2 fun y J' j₀ hJ' hy => ?_
  choose J hJ using fun ψ : D'.P.A.left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ y)
  have hJ : Good D.P.L y J := hJ
  obtain ⟨p, hp⟩ := exists_chart hM₀ (φ (Φ y))
  have e₁ := hth _ φ' y p j₀ ((congrArg (fun g => g y ∈ M₀.U p) hs).mpr hp) hy
  have e₂ := val_of_isPullTerm h Φ y hJ p hp
  have e₃ := ExpTrans.sec_val wD _ _ _ Φ hc t t' (𝟙 _) y (ht _ (𝟙 _) y) hJ hJ'
  have e₄ := S _ (𝟙 _) y p (J Φ) j₀ (J' (𝟙 _)) hp (hJ Φ) hy (hJ' (𝟙 _))
  simp only [Category.id_comp] at e₃ e₄
  rw [IndivisibleSection.prod_fam_zero D' (ExpTrans.om wD y J J'), ExpTrans.om, Category.id_comp] at e₃
  rw [← hs, e₁, e₃, ← _root_.mul_assoc, ← Units.val_mul, e₄, Units.val_mul, _root_.mul_assoc] at e₂
  exact (Units.mul_right_inj _).1 e₂

end Term

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem dual_hom_ext {ρ ρ' : DualNumber R →+* R'} (h : ∀ r, ρ (TrivSqZeroExt.inl r) = ρ' (TrivSqZeroExt.inl r))
    (he : ρ DualNumber.eps = ρ' DualNumber.eps) : ρ = ρ' := RingHom.ext fun a => by
  have e : a = TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inl a.snd * DualNumber.eps := by ext <;> simp
  rw [e, map_add, map_add, map_mul, map_mul, h, h, he]

theorem dualMap_inl (φ : R →+* R') (a : R) : dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a) := by
  ext <;> simp [dualMap]

theorem dualMap_eps' (φ : R →+* R') : dualMap φ DualNumber.eps = DualNumber.eps := by
  ext <;> simp [dualMap]

theorem spMap_comp' {R'' : Type} [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem isLocalRing_trunc (A : Type) [CommRing A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1)) := by
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1) ≠ ⊤ := fun h => by
    have h' : Ideal.span {(PowerSeries.X : PowerSeries A)} = ⊤ :=
      top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self n.succ_ne_zero))
    have := (Ideal.span_singleton_eq_top.1 h').map (PowerSeries.constantCoeff (R := A))
    simp at this
  have := Ideal.Quotient.nontrivial_iff.2 hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

def truncMap (f : R →+* R') (n : ℕ) : PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R)} ^ (n + 1) →+*
    PowerSeries R' ⧸ Ideal.span {(PowerSeries.X : PowerSeries R')} ^ (n + 1) :=
  Ideal.quotientMap _ (PowerSeries.map f) (Ideal.map_le_iff_le_comap.1 (by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, PowerSeries.map_X]))

end Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}
  {W : Wit Y a χ} {A' : Type} [CommRing A'] [IsDomain A'] {b' : O →+* A'} {a' : ArcIn Dw l β A' b'} {f : A →+* A'}
  {p : Out.IsPullDeg f a.D₀ a'.D₀} {W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)}
  {hD : Out.IsPullDeg (PowerSeries.map f) W.P.D.toPre W'.P.D.toPre}
  {bc : W'.t.G ≅ (Over.pullback (Out.specOf (PowerSeries.map f))).obj W.t.G}

set_option maxHeartbeats 1600000 in

theorem lieImg_baseChange [IsLocalRing A] [IsLocalRing A']
    (hU : Out.IsPullUnif (PowerSeries.map f) hD bc W.P.U W'.P.U) (he : ∀ y, hD.xe (W'.e y) = W.e (p.xe y))
    (hs : W'.φ ≫ prj p = prj hD ≫ W.φ) (S : Sq W.w hD.w p.w W'.w)
    {ν : Out.GtPt a.D₀ (epsR A)} {ν' : Out.GtPt a'.D₀ (epsR A')} {v : epsR (PowerSeries A) ⟶ W.t.G}
    {v' : epsR (PowerSeries A') ⟶ W'.t.G} (hν : LetBC p ν ν') (hv : LieImg W ν v)
    (hv' : v'.left ≫ bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (PowerSeries.map f)) =
      spMap (dualMap (PowerSeries.map f)) ≫ v.left) : LieImg W' ν' v' := by
  intro n ρ' κ' vn' hρ₁ hρ₂ hκ₁ hκ₂ hb hf x
  obtain ⟨wL, -, -, -, lev⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ hD _ _ _ _ bc _ _).1 hU
  obtain ⟨h, hh, ⟨-, ht⟩, -⟩ := lev n
  obtain ⟨ho, Ht⟩ := ht (W'.e x)
  rw [he] at ho Ht
  obtain ⟨hg, Hν⟩ := hν.2 x
  have Hν := (maps_iff p.w _ _ _ _ _ _ _ (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hg) (fun _ => rfl)).1 Hν
  have := isLocalRing_trunc A n
  have := isLocalRing_trunc A' n
  have := ConstTan.isLocalRing_dual (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1))
  have := ConstTan.isLocalRing_dual (PowerSeries A' ⧸ Ideal.span {(PowerSeries.X : PowerSeries A')} ^ (n + 1))
  let I : Ideal (PowerSeries A) := Ideal.span {PowerSeries.X}
  let ρ : DualNumber (PowerSeries A) →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) := dualMap (Ideal.Quotient.mk _)
  let κ : DualNumber A →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) :=
    dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))
  let s : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ Sp (PowerSeries A ⧸ I ^ (n + 1)) := spMap (algebraMap _ _)
  have hs₀ : s ≫ Out.thick (PowerSeries A) I n = spMap ρ ≫ (epsR (PowerSeries A)).hom :=
    ((spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r =>
      (dualMap_inl (Ideal.Quotient.mk (I ^ (n + 1))) r).symm : _ = ρ.comp (algebraMap _ _)))).trans
      (spMap_comp' _ _).symm
  let vn : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (Out.thickObj (PowerSeries A) I n W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs₀])
  have hx : vn ≫ (Out.fstG I n W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have G := hv n ρ κ vn (dualMap_inl _) (dualMap_eps' _) (dualMap_inl _) (dualMap_eps' _)
    (pullback.lift_snd _ _ _) hx (p.xe x)
  let q := spMap (dualMap (truncMap f n))
  have hρ : spMap ρ' ≫ spMap (dualMap (PowerSeries.map f)) = q ≫ spMap ρ := by
    rw [spMap_comp', spMap_comp']
    refine congrArg spMap (dual_hom_ext (fun r => ?_) ?_)
    · simp only [RingHom.comp_apply, ρ, dualMap_inl, hρ₁]
      rfl
    · simp only [RingHom.comp_apply, ρ, dualMap_eps', hρ₂]
  have hκ : spMap κ' ≫ spMap (dualMap f) = q ≫ spMap κ := by
    rw [spMap_comp', spMap_comp']
    refine congrArg spMap (dual_hom_ext (fun r => ?_) ?_)
    · simp only [RingHom.comp_apply, κ, dualMap_inl, hκ₁]
      rw [← PowerSeries.map_C]
      rfl
    · simp only [RingHom.comp_apply, κ, dualMap_eps', hκ₂]
  have hvn : vn' ≫ h = q ≫ vn := by
    have := thick_mono (PowerSeries A) I n
    have : Mono (Out.fstG I n W.t.G).left := inferInstanceAs (Mono (pullback.fst _ _))
    rw [← cancel_mono (Out.fstG I n W.t.G).left, Category.assoc, hh, ← Category.assoc, hf, Category.assoc]
    erw [hv']
    rw [← Category.assoc, hρ, Category.assoc, Category.assoc, hx]
  refine genRelR_baseChange hs S W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB ((W.P.U.gt n).t_gen _) (ν.isGen _) ho Ht Hν
    hvn hκ (fun k => (pull_grp p).1.hom_ext ?_ ?_) G
  · exact comp_eq_of_squares hs (ho k) (hg k) hvn hκ (G.1 k)
  · have a₁ : W'.P.D.toPre.Oφ (W'.P.U.gt n).pG (W'.e x) k ≫ W'.P.D.toPre.P.A.hom =
        (Out.thickObj (PowerSeries A') (Ideal.span {PowerSeries.X}) n W'.t.G).hom ≫ Out.thick _ _ n := by
      fin_cases k <;> exact Over.w _
    have a₂ : Out.DegPre.gtφT a'.D₀ (epsR A') ν'.b x k ≫ a'.D₀.P.A.hom = spMap (algebraMap A' (DualNumber A')) := by
      fin_cases k <;> exact Over.w _
    have a₃ : W'.φ ≫ a'.D₀.P.A.hom = W'.P.D.toPre.P.A.hom ≫ spMap (PowerSeries.C (R := A')) := W'.spec.1.1.w
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) a₂)).symm)
    rw [a₃, Category.assoc, reassoc_of% a₁, reassoc_of% hb]
    refine (congrArg (_ ≫ ·) (spMap_comp' _ _)).trans ((spMap_comp' _ _).trans (Eq.trans ?_ (spMap_comp' _ _).symm))
    exact congrArg spMap (RingHom.ext fun r => (hκ₁ r).symm)

set_option maxHeartbeats 1600000 in

theorem thetaOf_baseChange (hG : Out.GlobalFnsSt)
    (hU : Out.IsPullUnif (PowerSeries.map f) hD bc W.P.U W'.P.U)
    (hs : W'.φ ≫ prj p = prj hD ≫ W.φ) (S : Sq W.w hD.w p.w W'.w) (m : SABMap W'.t W.t (spMap (PowerSeries.map f)))
    (hm : m.φ = bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (PowerSeries.map f)))
    {w : LB.Iso W'.t.PP.L (W.t.PP.L.pull m.φ)} {th : a.D₀.P.L.Sec} {th' : a'.D₀.P.L.Sec} {θ : LB.Sec W.t.PP.L}
    {θ' : LB.Sec W'.t.PP.L} {θ₂ : LB.Sec (W.t.PP.L.pull m.φ)} (hw : RigIso m w) (hth : ThBC p th th')
    (hθ : ThetaOf W th θ) (h₁ : PullSec m.φ θ θ₂) (h₂ : IsoMaps w θ' θ₂) : ThetaOf W' th' θ' := by
  obtain ⟨σ, fam, θ₁, hE, hT, h0, hθ⟩ := hθ
  obtain ⟨th₂, t₁, t₂⟩ := hth
  obtain ⟨wL, gL, heL, mL, lev⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ hD _ _ _ _ bc _ _).1 hU
  obtain ⟨θ₁', hθ', R⟩ := srel_of_rig (UT.PullDescent.surj_base W'.P.U.toUnifPre hG).1 W.P.bundle W'.P.bundle hm m.base
    gL hw.1 mL hw.2 hθ (srel_of h₁ h₂)
  obtain ⟨σ', h0'⟩ := exists_h0Sec θ₁'
  choose fam' hf' using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ W.P.D.toPre.P.isLB W'.P.D.toPre.P.isLB hD.w
    hD.w_gen (Fin 4) (W'.P.D.toPre.famφB x) (W.P.D.toPre.famφB (hD.xe x)) (Out.DegPre.famε 1) _
    (ExpGTrans.famφB_pull hD x) (fam (hD.xe x))).exists
  refine ⟨σ', fam', θ₁', fun n => ?_, ?_, h0', hθ'⟩
  · obtain ⟨h, hh⟩ := lev n
    refine expandsAt_transport _ _ _ _ _ _ _ _ _ _ W.P.U.toUnifPre W'.P.U.toUnifPre _ hD.w hD.xe _ wL hD.w_gen gL
      (ExpGTrans.famφB_pull hD) n n 1 h hh σ σ' fam fam' (fun Z r z i j hi hj => ?_) hf' (hE n)
    rw [gs_h0Sec h0 _ z i (hi 0), gs_h0Sec h0' _ z j (hj 0), R Z r z _ _ (hi 0) (hj 0)]
    simp only [Fin.prod_univ_one, Category.comp_id, Nat.cast_one, zpow_one]
  · have a₁ := hf' 0
    have a₂ := ExpGTrans.famφB_pull hD 0
    rw [map_zero] at a₁ a₂
    exact isPullTerm_baseChange hs S a.D₀.P.isLB (srel_of t₁ t₂) a₂ a₁ hT

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A'] (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A') (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)), InBC f a a' p → WitBC f p W W' → ∃ m : SABMap W'.t W.t (spMap (PowerSeries.map f)), W'.m.φ = m.φ ≫ W.m.φ ∧ (∀ ν ν' v (v' : epsR (PowerSeries A') ⟶ W'.t.G), LetBC p ν ν' → LieImg W ν v → v'.left ≫ m.φ = spMap (dualMap (PowerSeries.map f)) ≫ v.left → LieImg W' ν' v') ∧ ∀ (w : LB.Iso W'.t.PP.L (W.t.PP.L.pull m.φ)) th th' θ (θ' : LB.Sec W'.t.PP.L) θ₂, RigIso m w → ThBC p th th' → ThetaOf W th θ → PullSec m.φ θ θ₂ → IsoMaps w θ' θ₂ → ThetaOf W' th' θ' := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W A' _ _ _ _ b' a' f p W' _
    ⟨hD, bc, _, hU, hφ, he, hs, w₁, w₂, e, T₁, T₂⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W.m W'.m
  have hm' : m.φ = bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (PowerSeries.map f)) := by
    refine W.m.cart.1.hom_ext (hm.symm.trans hφ) (m.cart.1.w.trans ?_)
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) (Over.w bc.hom).symm
  have S := sq_of_tri hs e T₁ T₂
  exact ⟨m, hm, fun ν ν' v v' hν hv hv' => lieImg_baseChange hU he hs S hν hv (hm' ▸ hv'),
    fun w th th' θ θ' θ₂ hw hth hθ h₁ h₂ => thetaOf_baseChange hL.globalFns hU hs S m hm' hw hth hθ h₁ h₂⟩

end GlobalTheory.ArcBaseChange
