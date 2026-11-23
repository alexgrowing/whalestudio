import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.FramePull

open GlobalTheory.ConstFam

section General

variable {X Y Y' W W' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem gs_comp (ρ : W' ⟶ W) (r : W ⟶ Y) (z : W') (U : Y.Opens) (h : r (ρ z) ∈ U) (a : Γ(Y, U)) :
    gs (ρ ≫ r) z U a = (ρ.stalkMap z).hom (gs r (ρ z) U a) := by
  rw [← gs_pull ρ r z U h, gs_stalkMap ρ z _ h, gs_pull (𝟙 _) r (ρ z) U h, Category.id_comp]

theorem gs_one (r : W ⟶ Y) (z : W) : gs r z ⊤ 1 = 1 := by
  rw [gs_eq r z ⊤ trivial, map_one, map_one]

theorem sval_comp {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (ρ : W' ⟶ W) (r : W ⟶ Y) (z : W')
    {J : (W' ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (ρ ≫ r) z J = (ρ.stalkMap z).hom (sval s r (ρ z) (fun ψ => J (ρ ≫ ψ))) := by
  rw [sval_of s (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp ρ r z _ (Set.mem_iInter.2 fun k => hJ (ρ ≫ r ≫ φ k)) _

theorem exists_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      ∀ (W : Scheme.{0}) (r : W ⟶ Y') (z : W) (J), Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨DVR.pullSec L φ ε s h, fun W r z J hJ => DVR.SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

theorem sec_ext_of_inj (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ y J, Good L y J → sval u κ y J = sval t κ y J) : u = t := by
  have : u.f = t.f := funext fun j => by
    refine hκ (LB.wchart L φ j) (fn_ext fun y hy => ?_)
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    refine (gs_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') κ y _ hy _).symm)
    rw [Category.id_comp]
    exact (sec_trans u κ y hy (Good.mem hI φ κ)).trans ((congrArg _ (h y I hI)).trans
      (sec_trans t κ y hy (Good.mem hI φ κ)).symm)
  cases u; cases t; cases this; rfl

end General

section OneBase

variable {S : Scheme.{0}} {G : Over S} {L : LB G.left} {N : ℕ}

abbrev sv {T : Over S} (s : LB.Sec (LPow G L (N : ℤ) T)) {W : Scheme.{0}} (r : W ⟶ (T ⊗ G).left) (z : W)
    (J : (W ⟶ G.left) → L.ι) : W.presheaf.stalk z :=
  sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s r z J

theorem lin_iff {T T' : Over S} (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (c : Fin n → Γ(T'.left, ⊤)) (s : LB.Sec (LPow G L (N : ℤ) T')) :
    Lin G L N h b c s ↔ ∀ (W : Scheme.{0}) (r : W ⟶ (T' ⊗ G).left) (z : W) (J), Good L z J →
      sv s r z J = ∑ i, gs (r ≫ (fst T' G).left) z ⊤ (c i) * sv (b i) (r ≫ (h ▷ G).left) z J := by
  constructor
  · intro H W r z J hJ
    have e := congrArg (r.stalkMap z).hom (H (r z) (fun ψ => J (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ)))
    rw [map_sum] at e
    refine ((congrArg (fun q => sv s q z J) (Category.comp_id r).symm).trans (sval_comp _ r _ z hJ)).trans
      (e.trans (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_mul, ← gs_comp r _ z ⊤ trivial]
    exact congrArg _ (sval_comp _ r _ z hJ).symm
  · intro H z J hJ
    simpa only [Category.id_comp] using H _ (𝟙 _) z J hJ

def IsPull {T T' : Over S} (u : T' ⟶ T) (s : LB.Sec (LPow G L (N : ℤ) T)) (s' : LB.Sec (LPow G L (N : ℤ) T')) : Prop :=
  ∀ (W : Scheme.{0}) (r : W ⟶ (T' ⊗ G).left) (z : W) (J), Good L z J → sv s' r z J = sv s (r ≫ (u ▷ G).left) z J

theorem exists_isPull {T T' : Over S} (u : T' ⟶ T) (s : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s', IsPull u s s' :=
  exists_pull (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (u ▷ G).left
    (φ' := fun _ : Fin 1 => (snd T' G).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])

theorem isPull_of_lin {T T' : Over S} {u : T' ⟶ T} {s : LB.Sec (LPow G L (N : ℤ) T)} {s' : LB.Sec (LPow G L (N : ℤ) T')}
    (H : Lin G L N u (fun _ : Fin 1 => s) (fun _ => 1) s') : IsPull u s s' := fun W r z J hJ => by
  rw [(lin_iff _ _ _ _).1 H W r z J hJ, Fin.sum_univ_one, gs_one, _root_.one_mul]

theorem IsPull.retract {T T' : Over S} {p : T' ⟶ T} {e : T ⟶ T'} (he : e ≫ p = 𝟙 T)
    {s : LB.Sec (LPow G L (N : ℤ) T)} {s' : LB.Sec (LPow G L (N : ℤ) T')} (H : IsPull p s s') : IsPull e s' s :=
  fun W r z J hJ => by
    rw [H W _ z J hJ, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, he, id_whiskerRight, Over.id_left,
      Category.comp_id]

theorem lin_pull {T T' : Over S} (u : T' ⟶ T) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} {s s'} (hb : ∀ i, IsPull u (b i) (b' i)) (hs : IsPull u s s')
    {c : Fin n → Γ(T.left, ⊤)} (H : Lin G L N (𝟙 T) b c s) :
    Lin G L N (𝟙 T') b' (fun i => u.left.appTop.hom (c i)) s' := by
  rw [lin_iff] at H ⊢
  intro W r z J hJ
  rw [hs W r z J hJ, H W _ z J hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb i W _ z J hJ, id_whiskerRight, id_whiskerRight, Over.id_left, Over.id_left, Category.comp_id, Category.comp_id,
    Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc]
  exact congrArg (· * _) (gs_pull _ u.left z ⊤ trivial _).symm

theorem basis_of_retract {T T' : Over S} {p : T' ⟶ T} {e : T ⟶ T'} (he : e ≫ p = 𝟙 T) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')}
    (hb : ∀ i, IsPull p (b i) (b' i)) (H : BasisAlong G L N (𝟙 T') b') : BasisAlong G L N (𝟙 T) b := by
  intro s
  obtain ⟨s', hs⟩ := exists_isPull p s
  obtain ⟨c, hc, hu⟩ := H s'
  refine ⟨_, lin_pull e (fun i => (hb i).retract he) (hs.retract he) hc, fun c' hc' => ?_⟩
  rw [← hu _ (lin_pull p hb hs hc')]
  funext i
  have : p.left.appTop ≫ e.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, he, Over.id_left, Scheme.Hom.id_appTop]
  exact (congrArg (fun q => q.hom (c' i)) this).symm

theorem whisker_isPullback {T T' : Over S} (u : T' ⟶ T) :
    IsPullback (u ▷ G).left (fst T' G).left (fst T G).left u.left := by
  refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
    (IsPullback.of_hasPullback T.hom G.hom).flip
  · rw [← Over.comp_left, whiskerRight_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom G.hom).flip
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

theorem basis_of_isFrame [Flat G.hom] (hL : L.IsLB) {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (x : Sp (FractionRing R) ⟶ S) {n : ℕ} (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x)))
    (H : IsFrame G L N x f) : BasisAlong G L N (𝟙 _) f := by
  let K := FractionRing R
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let C : K →+* PowerSeries K := PowerSeries.C
  have hV : CDvr (PowerSeries K) := ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
    charZero_of_injective_ringHom (f := C) C.injective⟩
  have hh : spMap ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp C) ≫ x =
      jK (PowerSeries K) ≫ spMap C ≫ x := by
    rw [← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨b', hb', hs⟩ := H (PowerSeries K) hV (C.comp (algebraMap R K))
    ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp C) (fun _ => rfl) (spMap C ≫ x) hh
  let p : Over.mk (spMap C ≫ x) ⟶ Over.mk x := Over.homMk (spMap C) rfl
  have hcc : spMap (PowerSeries.constantCoeff (R := K)) ≫ spMap C = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, PowerSeries.constantCoeff_comp_C, CommRingCat.ofHom_id, Spec.map_id]
  let e : Over.mk x ⟶ Over.mk (spMap C ≫ x) := Over.homMk (spMap (PowerSeries.constantCoeff (R := K)))
    (by show _ ≫ spMap C ≫ x = x; rw [← Category.assoc, hcc, Category.id_comp])
  refine basis_of_retract (p := p) (e := e) (Over.OverMorphism.ext hcc) (fun i => ?_) hb'
  obtain ⟨s, h₁, h₂⟩ := hs i
  obtain ⟨f', hf'⟩ := exists_isPull p (f i)
  let κ : Over.mk (jK (PowerSeries K) ≫ spMap C ≫ x) ⟶ Over.mk (spMap C ≫ x) := Over.homMk (jK (PowerSeries K)) rfl
  have : IsDominant (jK (PowerSeries K)) := DVR.isDominant_jK
  have : IsSchemeTheoreticallyDominant κ.left := IsSchemeTheoreticallyDominant.of_isDominant (jK (PowerSeries K))
  have : QuasiCompact κ.left := inferInstanceAs (QuasiCompact (jK (PowerSeries K)))
  have : Flat (fst (Over.mk (spMap C ≫ x)) G).left := inferInstanceAs (Flat (pullback.fst (spMap C ≫ x) G.hom))
  have : IsSchemeTheoreticallyDominant (κ ▷ G).left :=
    IsSchemeTheoreticallyDominant.of_isPullback (whisker_isPullback κ).flip
  have : QuasiCompact (κ ▷ G).left := MorphismProperty.of_isPullback (whisker_isPullback κ).flip inferInstance
  have : f' = b' i := sec_ext_of_inj (φ := fun _ : Fin 1 => (snd (Over.mk (spMap C ≫ x)) G).left)
    (ε := fun _ => (N : ℤ)) hL (κ ▷ G).left (κ ▷ G).left.app_injective fun y J hJ => by
      have a₁ := isPull_of_lin h₁ _ (𝟙 _) y J hJ
      have a₂ := isPull_of_lin h₂ _ (𝟙 _) y J hJ
      rw [Category.id_comp] at a₁ a₂
      refine (hf' _ _ y J hJ).trans (Eq.trans ?_ (a₁.symm.trans a₂))
      rw [← Over.comp_left, ← comp_whiskerRight]
      congr 3
      exact Over.OverMorphism.ext (Spec.map_comp _ _).symm
  exact this ▸ hf'

end OneBase

section TwoBases

variable {S Z : Scheme.{0}} {G₀ : Over S} {G : Over Z} {L₀ : LB G₀.left} {L : LB G.left} {F : G.left ⟶ G₀.left}
  {π : Z ⟶ S} {N : ℕ}

def TransportedAlt (w : LB.Iso L (L₀.pull F)) {T : Over Z} {T₀ : Over S} (Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left)
    (a : LB.Sec (LPow G L (N : ℤ) T)) (t : LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)) : Prop :=
  ∀ (W : Scheme.{0}) (r : W ⟶ (T ⊗ G).left) (z : W) (J₀ J), Good L₀ z J₀ → Good L z J →
    sv t (r ≫ Φ) z J₀ = (wVal w z J₀ J (r ≫ (snd T G).left) ^ (N : ℤ)).val * sv a r z J

variable {w : LB.Iso L (L₀.pull F)}

theorem exists_thr_down (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {T : Over Z} {T₀ : Over S}
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (hΦ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F)
    (t : LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)) : ∃ a, TransportedAlt w Φ a t := by
  have hψ : ∀ _ : Fin 1, (snd T G).left ≫ F = Φ ≫ (snd T₀ G₀).left := fun _ => hΦ.symm
  obtain ⟨a, ha⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T G).left) (φ := fun _ : Fin 1 => (snd T₀ G₀).left)
    (ε := fun _ => (N : ℤ)) hw hL₀ hL hψ t
  exact ⟨a, fun W r z J₀ J h₀ h => (ha.sval hψ r h₀ h).trans (by rw [Fin.prod_univ_one])⟩

theorem exists_thr_up (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {T : Over Z} {T₀ : Over S}
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} {Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left}
    (hΨ : Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left) (h : Φ ≫ Ψ = 𝟙 _)
    (a : LB.Sec (LPow G L (N : ℤ) T)) : ∃ t, TransportedAlt w Φ a t := by
  obtain ⟨t, ht⟩ := exists_sec_up (φ' := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ))
    ((isGen_iff w).1 hw) hL₀ hL a
  have H : SecThrough w (fun _ : Fin 1 => (snd T G).left) (fun _ => (snd T G).left ≫ F) (fun _ => (N : ℤ)) a t (𝟙 _) :=
    fun Z r z p q hp hq => by
      rw [Category.comp_id]
      exact ht Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  obtain ⟨t', ht'⟩ := exists_pull t Ψ (φ' := fun _ : Fin 1 => (snd T₀ G₀).left) (fun _ => hΨ)
  refine ⟨t', fun W r z J₀ J h₀ hJ => (ht' W _ z J₀ h₀).trans ?_⟩
  rw [Category.assoc, h]
  exact (H.sval (fun _ => (Category.id_comp _).symm) r h₀ hJ).trans (by rw [Fin.prod_univ_one])

theorem lin_at_iff {T T' : Over Z} {T₀ T₀' : Over S} {h : T' ⟶ T} {h₀ : T₀' ⟶ T₀}
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} {Φ' : (T' ⊗ G).left ⟶ (T₀' ⊗ G₀).left}
    (hc : Φ' ≫ (h₀ ▷ G₀).left = (h ▷ G).left ≫ Φ) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b₀ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)} (hb : ∀ i, TransportedAlt w Φ (b i) (b₀ i))
    {s : LB.Sec (LPow G L (N : ℤ) T')} {s₀ : LB.Sec (LPow G₀ L₀ (N : ℤ) T₀')} (hs : TransportedAlt w Φ' s s₀)
    {W : Scheme.{0}} (r : W ⟶ (T' ⊗ G).left) (z : W) {J₀ J} (hJ₀ : Good L₀ z J₀) (hJ : Good L z J)
    (c : Fin n → W.presheaf.stalk z) :
    sv s₀ (r ≫ Φ') z J₀ = ∑ i, c i * sv (b₀ i) ((r ≫ Φ') ≫ (h₀ ▷ G₀).left) z J₀ ↔
      sv s r z J = ∑ i, c i * sv (b i) (r ≫ (h ▷ G).left) z J := by
  have e : ∀ i, sv (b₀ i) ((r ≫ Φ') ≫ (h₀ ▷ G₀).left) z J₀ =
      (wVal w z J₀ J (r ≫ (snd T' G).left) ^ (N : ℤ)).val * sv (b i) (r ≫ (h ▷ G).left) z J := fun i => by
    rw [Category.assoc, hc, ← Category.assoc, hb i W _ z J₀ J hJ₀ hJ, Category.assoc, ← Over.comp_left,
      whiskerRight_snd]
  rw [hs W r z J₀ J hJ₀ hJ]
  simp only [e, mul_left_comm (c _), ← Finset.mul_sum]
  exact Units.mul_right_inj _

theorem exists_cmp (hF : IsPullback F G.hom G₀.hom π) {T : Over Z} {T₀ : Over S} (u : T.left ⟶ T₀.left)
    (hu : u ≫ T₀.hom = T.hom ≫ π) : ∃ Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left,
      Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u ∧ Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F :=
  ⟨pullback.lift ((fst T G).left ≫ u) ((snd T G).left ≫ F) (by
    rw [Category.assoc, hu, Category.assoc, hF.w, ← Category.assoc, Over.w, ← Category.assoc, Over.w]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem prod_ext {T₀ : Over S} {W : Scheme.{0}} {a b : W ⟶ (T₀ ⊗ G₀).left}
    (h₁ : a ≫ (fst T₀ G₀).left = b ≫ (fst T₀ G₀).left) (h₂ : a ≫ (snd T₀ G₀).left = b ≫ (snd T₀ G₀).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem cmp_comm {T T' : Over Z} {T₀ T₀' : Over S} {h : T' ⟶ T} {h₀ : T₀' ⟶ T₀}
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} {Φ' : (T' ⊗ G).left ⟶ (T₀' ⊗ G₀).left} {u : T.left ⟶ T₀.left}
    {u' : T'.left ⟶ T₀'.left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) (b₁ : Φ' ≫ (fst T₀' G₀).left = (fst T' G).left ≫ u')
    (b₂ : Φ' ≫ (snd T₀' G₀).left = (snd T' G).left ≫ F) (e : u' ≫ h₀.left = h.left ≫ u) :
    Φ' ≫ (h₀ ▷ G₀).left = (h ▷ G).left ≫ Φ := by
  apply prod_ext
  · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, reassoc_of% b₁, e, Category.assoc, a₁,
      ← Category.assoc (h ▷ G).left, ← Over.comp_left, whiskerRight_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, ← Over.comp_left, whiskerRight_snd, b₂, Category.assoc, a₂,
      ← Category.assoc (h ▷ G).left, ← Over.comp_left, whiskerRight_snd]

theorem lin_one_down (hL₀ : L₀.IsLB) {T T' : Over Z} {T₀ T₀' : Over S} {h : T' ⟶ T} {h₀ : T₀' ⟶ T₀}
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} {Φ' : (T' ⊗ G).left ⟶ (T₀' ⊗ G₀).left}
    (hc : Φ' ≫ (h₀ ▷ G₀).left = (h ▷ G).left ≫ Φ) {b : LB.Sec (LPow G L (N : ℤ) T)}
    {b₀ : LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)} (hb : TransportedAlt w Φ b b₀)
    {s : LB.Sec (LPow G L (N : ℤ) T')} {s₀ : LB.Sec (LPow G₀ L₀ (N : ℤ) T₀')} (hs : TransportedAlt w Φ' s s₀)
    (H : Lin G₀ L₀ N h₀ (fun _ : Fin 1 => b₀) (fun _ => 1) s₀) : Lin G L N h (fun _ : Fin 1 => b) (fun _ => 1) s := by
  rw [lin_iff] at H ⊢
  intro W r z J hJ
  obtain ⟨J₀, hJ₀⟩ := exists_good' hL₀ z
  have := H W (r ≫ Φ') z J₀ hJ₀
  simp only [gs_one] at this ⊢
  exact (lin_at_iff hc (fun _ : Fin 1 => hb) hs r z hJ₀ hJ (fun _ => 1)).1 this

theorem basis_down (hF : IsPullback F G.hom G₀.hom π) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {V : Scheme.{0}}
    (χ : V ⟶ Z) {Φ : (Over.mk χ ⊗ G).left ⟶ (Over.mk (χ ≫ π) ⊗ G₀).left}
    (a₁ : Φ ≫ (fst (Over.mk (χ ≫ π)) G₀).left = (fst (Over.mk χ) G).left)
    (a₂ : Φ ≫ (snd (Over.mk (χ ≫ π)) G₀).left = (snd (Over.mk χ) G).left ≫ F) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk χ))} {b₀ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) (Over.mk (χ ≫ π)))}
    (hb : ∀ i, TransportedAlt w Φ (b i) (b₀ i)) (H : BasisAlong G₀ L₀ N (𝟙 _) b₀) : BasisAlong G L N (𝟙 _) b := by
  have w₀ : (snd (Over.mk (χ ≫ π)) G₀).left ≫ G₀.hom = ((fst (Over.mk (χ ≫ π)) G₀).left ≫ χ) ≫ π := by
    rw [Category.assoc]; exact pullback.condition.symm
  obtain ⟨Ψ, c₁, c₂⟩ : ∃ Ψ : (Over.mk (χ ≫ π) ⊗ G₀).left ⟶ (Over.mk χ ⊗ G).left,
      Ψ ≫ (fst (Over.mk χ) G).left = (fst (Over.mk (χ ≫ π)) G₀).left ∧
      Ψ ≫ (snd (Over.mk χ) G).left = hF.lift _ _ w₀ :=
    ⟨pullback.lift (fst (Over.mk (χ ≫ π)) G₀).left (hF.lift _ _ w₀) (hF.lift_snd _ _ w₀).symm,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have c₃ : Ψ ≫ (snd (Over.mk χ) G).left ≫ F = (snd (Over.mk (χ ≫ π)) G₀).left := by
    rw [reassoc_of% c₂, hF.lift_fst]
  have i₁ : Ψ ≫ Φ = 𝟙 _ := prod_ext (by rw [Category.assoc, a₁, c₁, Category.id_comp])
    (by rw [Category.assoc, a₂, c₃, Category.id_comp])
  have i₂ : Φ ≫ Ψ = 𝟙 _ := prod_ext (by rw [Category.assoc, c₁, a₁, Category.id_comp]) (by
    rw [Category.id_comp]
    apply hF.hom_ext
    · rw [Category.assoc, Category.assoc, c₃, a₂]
    · rw [Category.assoc, Category.assoc, reassoc_of% c₂, hF.lift_snd, reassoc_of% a₁]
      exact pullback.condition)
  have hc : Φ ≫ (𝟙 (Over.mk (χ ≫ π)) ▷ G₀).left = (𝟙 (Over.mk χ) ▷ G).left ≫ Φ := by
    rw [id_whiskerRight, id_whiskerRight, Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  intro s
  obtain ⟨s₀, hs⟩ := exists_thr_up hw hL₀ hL c₃ i₂ s
  refine (existsUnique_congr fun c => ?_).1 (H s₀)
  rw [lin_iff, lin_iff]
  constructor
  · intro H W r z J hJ
    obtain ⟨J₀, hJ₀⟩ := exists_good' hL₀ z
    have := H W (r ≫ Φ) z J₀ hJ₀
    rw [Category.assoc r Φ (fst (Over.mk (χ ≫ π)) G₀).left, a₁] at this
    exact (lin_at_iff hc hb hs r z hJ₀ hJ _).1 this
  · intro H W r z J₀ hJ₀
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := (lin_at_iff hc hb hs (r ≫ Ψ) z hJ₀ hJ _).2 (H W (r ≫ Ψ) z J hJ)
    rw [Category.assoc r Ψ Φ, i₁, Category.comp_id, Category.assoc r Ψ, c₁] at this
    exact this

theorem exists_isFrame (hF : IsPullback F G.hom G₀.hom π) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB)
    {R₁ R : Type} [CommRing R₁] [IsDomain R₁] [CommRing R] [IsDomain R] (g : R₁ →+* R)
    (gam : FractionRing R₁ →+* FractionRing R) (hg : ∀ r, gam (algebraMap R₁ _ r) = algebraMap R _ (g r))
    (x₁ : Sp (FractionRing R₁) ⟶ S) (x : Sp (FractionRing R) ⟶ Z) (hx : x ≫ π = spMap gam ≫ x₁) {n : ℕ}
    (f₁ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) (Over.mk x₁))) (H : IsFrame G₀ L₀ N x₁ f₁) :
    ∃ f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x)), IsFrame G L N x f := by
  obtain ⟨Φ, a₁, a₂⟩ := exists_cmp hF (T := Over.mk x) (T₀ := Over.mk x₁) (spMap gam) hx.symm
  choose f hf using fun i => exists_thr_down hw hL₀ hL a₂ (f₁ i)
  refine ⟨f, fun W _ _ _ hW φ gam' hg' χ h => ?_⟩
  have e : spMap (gam'.comp gam) = spMap gam' ≫ spMap gam := Spec.map_comp _ _
  have h₀ : spMap (gam'.comp gam) ≫ x₁ = jK W ≫ χ ≫ π := by
    rw [e, Category.assoc, ← hx, reassoc_of% h]
  obtain ⟨b₀, hb₀, hs⟩ := H W hW (φ.comp g) (gam'.comp gam) (fun r => (congrArg gam' (hg r)).trans (hg' _)) (χ ≫ π) h₀
  obtain ⟨Φ₁, b₁, b₂⟩ := exists_cmp hF (T := Over.mk χ) (T₀ := Over.mk (χ ≫ π)) (𝟙 (Sp W)) (Category.id_comp _)
  obtain ⟨Φ₂, c₁, c₂⟩ := exists_cmp hF (T := Over.mk (jK W ≫ χ)) (T₀ := Over.mk (jK W ≫ χ ≫ π)) (𝟙 (Sp (FractionRing W)))
    ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  choose b hb using fun i => exists_thr_down hw hL₀ hL b₂ (b₀ i)
  refine ⟨b, basis_down hF hw hL₀ hL χ (b₁.trans (Category.comp_id _)) b₂ hb hb₀, fun i => ?_⟩
  obtain ⟨s₀, k₁, k₂⟩ := hs i
  obtain ⟨s, hs⟩ := exists_thr_down hw hL₀ hL c₂ s₀
  exact ⟨s, lin_one_down hL₀ (cmp_comm a₁ a₂ c₁ c₂ ((Category.id_comp _).trans e)) (hf i) hs k₁,
    lin_one_down hL₀ (cmp_comm b₁ b₂ c₁ c₂ ((Category.id_comp _).trans (Category.comp_id _).symm)) (hb i) hs k₂⟩

end TwoBases

theorem frame_pull : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S Z : Scheme.{0}) (t₀ : SAB H S) (t : SAB H Z) (π : Z ⟶ S) (_ : SABMap t t₀ π) (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [CommRing R] [IsDomain R] [CharZero R] (g : R₁ →+* R) (gam : FractionRing R₁ →+* FractionRing R), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R _ (g r)) → ∀ (x₁ : Sp (FractionRing R₁) ⟶ S) (x : Sp (FractionRing R) ⟶ Z), x ≫ π = spMap gam ≫ x₁ → PolAt t₀ x₁ → ∀ (N n : ℕ) (f₁ : Fin n → LB.Sec (LPow t₀.G t₀.PP.L (N : ℤ) (Over.mk x₁))), IsFrame t₀.G t₀.PP.L N x₁ f₁ → ∃ f : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk x)), IsFrame t.G t.PP.L N x f ∧ BasisAlong t.G t.PP.L N (𝟙 _) f := by
  intro _ _ E _ _ _ H S Z t₀ t π m R₁ R _ _ _ _ _ g gam hg x₁ x hx _ N n f₁ hf₁
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨f, hf⟩ := exists_isFrame m.cart.1 hw t₀.PP.isLB t.PP.isLB g gam hg x₁ x hx f₁ hf₁
  have := t.semi.smooth
  exact ⟨f, hf, basis_of_isFrame t.PP.isLB x f hf⟩

end GlobalTheory.FramePull
