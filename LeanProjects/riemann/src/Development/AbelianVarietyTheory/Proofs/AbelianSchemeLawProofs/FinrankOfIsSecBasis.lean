import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.SecTwist

variable {X X' Y Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem gs_finsum (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by
  simp only [gs_eq r z U h, map_sum]

theorem gs_cst (p : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (a : R) :
    gs r z W (GlobalTheory.AbLaw.cst p W a) = Tor.cst (r ≫ p) z a :=
  (gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _)

def cstHom (p : Y ⟶ Spec (CommRingCat.of R)) (y : Y) : R →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem cstHom_apply (p : Y ⟶ Spec (CommRingCat.of R)) (y : Y) (a : R) : cstHom p y a = Tor.cst p y a :=
  (gs_eq p y ⊤ trivial _).symm

def CmbAt (p : Y ⟶ Spec (CommRingCat.of R)) {N : LB Y} {n : ℕ} (b : Fin n → LB.Sec N) (r : Fin n → R)
    (s : LB.Sec N) (j : N.ι) (y : Y) : Prop :=
  gs (𝟙 Y) y (N.U j) (s.f j) = ∑ i, Tor.cst p y (r i) * gs (𝟙 Y) y (N.U j) ((b i).f j)

def Cmb (p : Y ⟶ Spec (CommRingCat.of R)) {N : LB Y} {n : ℕ} (b : Fin n → LB.Sec N) (r : Fin n → R)
    (s : LB.Sec N) : Prop := ∀ j, ∀ y ∈ N.U j, CmbAt p b r s j y

def Bas (p : Y ⟶ Spec (CommRingCat.of R)) (N : LB Y) {n : ℕ} (b : Fin n → LB.Sec N) : Prop :=
  ∀ s : LB.Sec N, ∃! r : Fin n → R, Cmb p b r s

theorem cmb_of_loc {p : Y ⟶ Spec (CommRingCat.of R)} {N : LB Y} {n : ℕ} {b : Fin n → LB.Sec N} {r : Fin n → R}
    {s : LB.Sec N} (h : ∀ y, ∃ j, y ∈ N.U j ∧ CmbAt p b r s j y) : Cmb p b r s := by
  intro j y hy
  obtain ⟨k, hk, e⟩ := h y
  unfold CmbAt at e ⊢
  rw [gs_compat s (𝟙 Y) y hy hk, e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_compat (b i) (𝟙 Y) y hy hk, mul_left_comm]

theorem sec_ext_loc {N : LB Y} {s t : LB.Sec N}
    (h : ∀ y, ∃ j, y ∈ N.U j ∧ gs (𝟙 Y) y (N.U j) (s.f j) = gs (𝟙 Y) y (N.U j) (t.f j)) : s = t := by
  have : s.f = t.f := funext fun j => fn_ext fun y hy => by
    obtain ⟨k, hk, e⟩ := h y
    rw [gs_compat s (𝟙 Y) y hy hk, gs_compat t (𝟙 Y) y hy hk, e]
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := t
  cases this
  rfl

theorem exists_rel {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B) :
    ∃ u : ∀ y : Y, A.ι → B.ι → (Y.presheaf.stalk y)ˣ,
      (∀ s : LB.Sec A, ∃ t : LB.Sec B, ∀ y a b, y ∈ A.U a → y ∈ B.U b →
        gs (𝟙 Y) y (B.U b) (t.f b) = (u y a b).val * gs (𝟙 Y) y (A.U a) (s.f a)) ∧
      (∀ t : LB.Sec B, ∃ s : LB.Sec A, ∀ y a b, y ∈ A.U a → y ∈ B.U b →
        gs (𝟙 Y) y (B.U b) (t.f b) = (u y a b).val * gs (𝟙 Y) y (A.U a) (s.f a)) := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullId A) (chartPullPull B (𝟙 Y) (𝟙 Y) rfl)
  have hw' := (isGen_iff w).1 hw
  have le : ∀ p : (PUnit → A.ι) × B.ι, (A.pull (𝟙 Y)).U p.1 ⊓ B.U p.2 ≤
      (B.pull (𝟙 Y)).U (fun _ => p.2) ⊓ A.U (p.1 PUnit.unit) := fun p y hy =>
    ⟨mem_pull.2 hy.2, mem_pull.1 hy.1⟩
  let w' : LB.Iso B (A.pull (𝟙 Y)) := ⟨fun p => (res (le p) (w.s (fun _ => p.2, p.1 PUnit.unit)))⁻¹⟩
  have e : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) a b, r z ∈ A.U a → r z ∈ B.U b →
      gw w' r z a b = (gw w r z b a)⁻¹ := fun Z r z a b ha hb =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (le (fun _ => a, b)) ⟨mem_pull.2 ha, hb⟩ _))
  have pw' : PGen w' := fun Z r z a a' b b' ha ha' hb hb' => by
    rw [e Z r z a b ha hb, e Z r z a' b' ha' hb', hw' Z r z b b' a a' hb hb' ha ha']
    simp only [Category.comp_id, mul_inv, inv_inv]
    rw [mul_comm (gm r z _ (A.g a a'))]
  refine ⟨fun y a b => gw w (𝟙 Y) y b a, fun s => ?_, fun t => ?_⟩
  · obtain ⟨t, ht⟩ := sec_pull_down pw' hA hB s
    refine ⟨t, fun y a b ha hb => ?_⟩
    have := ht _ (𝟙 Y) y a b ha hb
    rw [Category.comp_id, e _ _ y a b ha hb] at this
    rw [this, Units.mul_inv_cancel_left]
  · obtain ⟨s, hs⟩ := sec_pull_down hw' hB hA t
    refine ⟨s, fun y a b ha hb => ?_⟩
    have := hs _ (𝟙 Y) y b a hb ha
    rwa [Category.comp_id] at this

theorem Bas.of_iso {p : Y ⟶ Spec (CommRingCat.of R)} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B)
    {n : ℕ} {b : Fin n → LB.Sec A} (hb : Bas p A b) : ∃ b' : Fin n → LB.Sec B, Bas p B b' := by
  obtain ⟨u, h₁, h₂⟩ := exists_rel hA hB H
  choose F hF using h₁
  refine ⟨fun i => F (b i), fun t => ?_⟩
  obtain ⟨s, hs⟩ := h₂ t
  have key : ∀ r y a c, y ∈ A.U a → y ∈ B.U c → (CmbAt p b r s a y ↔ CmbAt p (fun i => F (b i)) r t c y) := by
    intro r y a c ha hc
    unfold CmbAt
    rw [hs y a c ha hc, ← (u y a c).mul_right_inj, Finset.mul_sum]
    refine Eq.congr rfl (Finset.sum_congr rfl fun i _ => ?_)
    rw [hF (b i) y a c ha hc, mul_left_comm]
  have key' : ∀ r, Cmb p b r s ↔ Cmb p (fun i => F (b i)) r t := fun r =>
    ⟨fun h c y hc => by
      obtain ⟨a, ha⟩ := exists_chart hA y
      exact (key r y a c ha hc).1 (h a y ha), fun h a y ha => by
      obtain ⟨c, hc⟩ := exists_chart hB y
      exact (key r y a c ha hc).2 (h c y hc)⟩
  simpa only [← key'] using hb s

def pullSec {A' : LB X'} {A : LB X} {h : X' ⟶ X} (c : ChartPull A' A h) (s : LB.Sec A) : LB.Sec A' where
  f i := (X'.presheaf.map (homOfLE (c.le i)).op).hom ((h.app _).hom (s.f (c.idx i)))
  compat i j := fn_ext fun y hy => by
    have v : ∀ i, y ∈ A'.U i → gs (𝟙 X') y (A'.U i) ((X'.presheaf.map (homOfLE (c.le i)).op).hom
        ((h.app _).hom (s.f (c.idx i)))) = gs h y (A.U (c.idx i)) (s.f (c.idx i)) := fun i hi =>
      (gs_res _ y _ hi _).trans ((gs_pull (𝟙 X') h y _ (c.le i hi) _).trans (by rw [Category.id_comp]))
    rw [gs_res _ y inf_le_left hy, gs_mul _ y _ hy, gs_res _ y inf_le_right hy, gs_unit _ y _ hy, v i hy.1, v j hy.2, c.g y i j hy.1 hy.2]
    exact gs_compat s h y (c.le i hy.1) (c.le j hy.2)

theorem gs_pullSec {A' : LB X'} {A : LB X} {h : X' ⟶ X} (c : ChartPull A' A h) (s : LB.Sec A) (r : Z ⟶ X') (z : Z)
    (i : A'.ι) (hi : r z ∈ A'.U i) :
    gs r z (A'.U i) ((pullSec c s).f i) = gs (r ≫ h) z (A.U (c.idx i)) (s.f (c.idx i)) :=
  (gs_res _ z _ hi _).trans (gs_pull r h z _ (c.le i hi) _)

theorem perf_sec {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) (g : R →+* R') {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
    ∃ E : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0} ≃ LB.Sec (M.pull π),
      ∀ v i (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z), π (r z) ∈ Q.W i →
        gs r z ((M.pull π).U (fun _ => Q.ch i)) ((E v).f (fun _ => Q.ch i)) =
          ∑ k, Tor.cst (r ≫ f') z (v.1 k) * gs (r ≫ π) z (Q.W i) (Q.u k i) := by
  obtain ⟨E, hE⟩ := Q.sec R' g X' π f' h
  refine ⟨E, fun v i Z r z hz => ?_⟩
  have hz' : r z ∈ π ⁻¹ᵁ Q.W i := hz
  refine (gs_res r z (le_pull M π (Q.le i)) hz' _).symm.trans ((congrArg (gs r z _) (hE v i)).trans ?_)
  rw [gs_finsum r z _ hz']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gs_mul r z _ hz', gs_cst f' _ r z hz', gs_pull r π z _ hz]

theorem perf_cover {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) (x : X) : ∃ i, x ∈ Q.W i :=
  TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, Q.W i by rw [Q.cover]; trivial)

theorem perf_bas {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) (g : R →+* R') {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {n : ℕ} (B : Matrix (Fin Q.a) (Fin n) R) (hB : Q.D₀ * B = 0)
    (hu : ∀ v : Fin Q.a → R', (Q.D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v) :
    ∃ b : Fin n → LB.Sec (M.pull π), Bas f' _ b := by
  obtain ⟨E, hE⟩ := perf_sec Q g h
  have ker : ∀ z : Fin n → R', (Q.D₀.map g).mulVec ((B.map g).mulVec z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_zero _ (map_zero g), Matrix.zero_mulVec]
  let b : Fin n → LB.Sec (M.pull π) := fun l => E ⟨_, ker (Pi.single l 1)⟩
  have cm : ∀ z i y, π y ∈ Q.W i → CmbAt f' b z (E ⟨_, ker z⟩) (fun _ => Q.ch i) y := by
    intro z i y hy
    unfold CmbAt
    simp only [b, hE _ i _ (𝟙 X') y hy, Category.id_comp, ← cstHom_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [← _root_.mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp [Matrix.mulVec, dotProduct, mul_comm, Pi.single_apply]
  refine ⟨b, fun s => ?_⟩
  obtain ⟨v, rfl⟩ := E.surjective s
  have key : ∀ z, Cmb f' b z (E v) ↔ (B.map g).mulVec z = v.1 := fun z => ⟨fun hc => by
    have : E ⟨_, ker z⟩ = E v := sec_ext_loc fun y => by
      obtain ⟨i, hi⟩ := perf_cover Q (π y)
      have hm : y ∈ (M.pull π).U (fun _ => Q.ch i) := mem_pull.2 (Q.le i hi)
      exact ⟨_, hm, (cm z i y hi).trans (hc _ y hm).symm⟩
    exact congrArg Subtype.val (E.injective this), fun hz => by
    obtain rfl : ⟨_, ker z⟩ = v := Subtype.ext hz
    refine cmb_of_loc fun y => ?_
    obtain ⟨i, hi⟩ := perf_cover Q (π y)
    exact ⟨_, mem_pull.2 (Q.le i hi), cm z i y hi⟩⟩
  simpa only [key] using hu v.1 v.2

theorem perf_lift {W : Scheme.{0}} (L : LB W) {K : Type} [Fintype K] (φ : K → (X ⟶ W)) (ε : K → ℤ)
    {f : X ⟶ Spec (CommRingCat.of R)} (Q : Perf f (LB.LinComb L φ ε)) (g : R →+* R') (hg : Function.Surjective g)
    {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {n : ℕ} (B : Matrix (Fin Q.a) (Fin n) R) (hB : Q.D₀ * B = 0)
    (hu : ∀ v : Fin Q.a → R', (Q.D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v)
    (sbar : LB.Sec (LB.LinComb L (fun k => π ≫ φ k) ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), IsPullSecLC L φ ε π s sbar := by
  obtain ⟨E, hE⟩ := perf_sec Q g h
  have h₀ : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, hE₀⟩ := perf_sec Q (RingHom.id R) h₀
  obtain ⟨v, hv⟩ := E.surjective (pullSec (chartPullOut L φ ε π _ fun _ => rfl) sbar)
  obtain ⟨z, hz, -⟩ := hu v.1 v.2
  choose z₀ hz₀ using fun l => hg (z l)
  have ker : (Q.D₀.map (RingHom.id R)).mulVec (B.mulVec z₀) = 0 := by
    rw [show Q.D₀.map (RingHom.id R) = Q.D₀ from rfl, Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  have hv₀ : ∀ k, g (B.mulVec z₀ k) = v.1 k := fun k => by
    rw [RingHom.map_mulVec, ← hz, show g ∘ z₀ = z from funext hz₀]
  refine ⟨pullSec (chartPullUnpull _ (𝟙 X) rfl) (E₀ ⟨_, ker⟩), fun j => ?_⟩
  have : sbar = pullSec (chartPullSame L _ φ ε π fun _ => rfl)
      (pullSec (chartPullUnpull _ (𝟙 X) rfl) (E₀ ⟨_, ker⟩)) := by
    refine sec_ext_loc fun y => ?_
    obtain ⟨i, hi⟩ := perf_cover Q (π y)
    have m₁ : π y ∈ (LB.LinComb L φ ε).U (Q.ch i) := Q.le i hi
    have m₂ : y ∈ (LB.LinComb L (fun k => π ≫ φ k) ε).U (Q.ch i) :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₁ k
    refine ⟨Q.ch i, m₂, ?_⟩
    have a₁ := gs_pullSec (chartPullOut L φ ε π _ fun _ => rfl) sbar (𝟙 X') y (fun _ => Q.ch i) (mem_pull.2 m₁)
    rw [← hv, hE v i _ (𝟙 X') y hi, Category.id_comp, Category.id_comp, Category.id_comp] at a₁
    have a₂ := gs_pullSec (chartPullSame L _ φ ε π fun _ => rfl)
      (pullSec (chartPullUnpull _ (𝟙 X) rfl) (E₀ ⟨_, ker⟩)) (𝟙 X') y (Q.ch i) m₂
    rw [Category.id_comp] at a₂
    have a₃ := gs_pullSec (chartPullUnpull _ (𝟙 X) rfl) (E₀ ⟨_, ker⟩) π y (Q.ch i) m₁
    rw [Category.comp_id] at a₃
    have a₄ := hE₀ ⟨_, ker⟩ i _ π y hi
    refine a₁.symm.trans (Eq.trans ?_ (a₂.trans (a₃.trans a₄)).symm)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Category.comp_id, h.w, ← hv₀ k]
    exact congrArg (· * _) (cst_comp f' g y _).symm
  exact congrArg (fun s => s.f j) this

theorem cmb_iff {p : Y ⟶ Spec (CommRingCat.of R)} {N : LB Y} {n : ℕ} (b : Fin n → LB.Sec N) (r : Fin n → R)
    (s : LB.Sec N) : Cmb p b r s ↔ ∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r i))) * (b i).f j := by
  have e : ∀ j, ∀ y ∈ N.U j, gs (𝟙 Y) y (N.U j) (∑ i, (Y.presheaf.map (homOfLE le_top).op).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r i))) * (b i).f j) =
      ∑ i, Tor.cst p y (r i) * gs (𝟙 Y) y (N.U j) ((b i).f j) := fun j y hy => by
    rw [gs_finsum _ y _ hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ y _ hy]
    exact congrArg (· * _) ((gs_cst p _ (𝟙 Y) y hy (r i)).trans (by rw [Category.id_comp]))
  exact forall_congr' fun j => ⟨fun h => fn_ext fun y hy => (h y hy).trans (e j y hy).symm,
    fun h y hy => (congrArg _ h).trans (e j y hy)⟩

theorem Bas.exists_unique {p : Y ⟶ Spec (CommRingCat.of R)} {N : LB Y} {n : ℕ} {b : Fin n → LB.Sec N}
    (hb : Bas p N b) (s : LB.Sec N) : ∃! r : Fin n → Γ(Spec (CommRingCat.of R), ⊤), ∀ j,
      s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom (r i)) * (b i).f j := by
  obtain ⟨r, hr, hu⟩ := hb s
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r i), (cmb_iff b r s).1 hr, fun r' hr' => ?_⟩
  have e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (r' i)) = r' i := fun i => Iso.hom_inv_id_apply _ _
  have := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (r' i)) ((cmb_iff b _ s).2 fun j => by
    simp only [e]; exact hr' j)
  funext i
  rw [← this, e]

theorem finrank_of_isSecBasis {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) (T : Over S)
    [Nontrivial Γ(T.left, ⊤)] {n : ℕ} (b : Fin n → LB.Sec (LPow A L a T)) (hb : IsSecBasis _ b) :
    Module.finrank Γ(T.left, ⊤) (SecM A L a T) = n := by
  let F := Fintype.linearCombination Γ(T.left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L a T))
  have hF : ∀ r j, (F r).1 j = ∑ i, ((T ⊗ A).left.presheaf.map (homOfLE le_top).op).hom
      ((fst T A).left.appTop.hom (r i)) * (b i).f j := fun r j => by
    simp only [F, Fintype.linearCombination_apply, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have bij : Function.Bijective F := by
    refine (Function.bijective_iff_existsUnique F).2 fun s => ?_
    obtain ⟨r, hr, hu⟩ := hb (SecM.toSec A s)
    refine ⟨r, Subtype.ext (funext fun j => (hF r j).trans (hr j).symm), fun r' hr' => hu r' fun j => ?_⟩
    exact (congrArg (fun t => t.1 j) hr').symm.trans (hF r' j)
  rw [← (LinearEquiv.ofBijective F bij).finrank_eq, Module.finrank_fin_fun]

theorem iso_of_gen_three (L : LB X) (a b c : Y ⟶ X) (m n k : ℤ)
    (w : LB.Gen (LB.LinComb L (K := Fin 3) ![a, b, c] ![m, n, -k])) (hw : w.IsGen) :
    LBIso (LB.LinComb L (K := Fin 1) (fun _ => c) (fun _ => k)) (LB.LinComb L (K := Fin 2) ![a, b] ![m, n]) := by
  have le : ∀ p : (Fin 2 → L.ι) × (Fin 1 → L.ι), LB.wchart L ![a, b] p.1 ⊓ LB.wchart L (fun _ : Fin 1 => c) p.2 ≤
      LB.wchart L ![a, b, c] ![p.1 0, p.1 1, p.2 0] := fun p y hy => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.1 1, Set.mem_iInter.1 hy.2 0]
  refine ⟨⟨fun p => res (le p) (w.s ![p.1 0, p.1 1, p.2 0])⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (gen_trans hw (𝟙 Y) y (le p hy.1) (le q hy.2)))).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div _ _ (𝟙 Y) y p q hy).trans ?_)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))))
  refine (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L _ _ (𝟙 Y) y p.1 q.1 hy.1.1 hy.2.1)
    (gm_linComb L _ _ (𝟙 Y) y p.2 q.2 hy.1.2 hy.2.2)).trans ?_
  rw [trF, Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_one, ← zpow_neg]
  rfl

def chartPullPw (L : LB X) (F : Y ⟶ X) (a : ℤ) :
    ChartPull (LB.LinComb L (K := Fin 1) (fun _ => F) (fun _ => a)) (pw L a) F where
  idx j := j 0
  le j y hy := Set.mem_iInter.1 hy 0
  g y j j' hj hj' := by
    refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans ?_
    rw [Fin.prod_univ_one, Category.id_comp]
    exact (map_zpow _ _ _).symm

theorem lbIso_refl {A : LB X} (hA : A.IsLB) : LBIso A A :=
  LBIso.chartPull (chartPullUnpull A _ rfl) (chartPullUnpull A _ rfl)
    (exists_iso_linComb hA (fun _ : PUnit => 𝟙 X) (fun _ => 1) fun _ _ _ => rfl)

section Transl

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem translT_translPt (x y : T ⟶ A) : translT A x ≫ translPt A y = translPt A (y * x) := by
  show translT A x ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A
  rw [MonObj.comp_mul, MonObj.comp_mul, translT, lift_fst_assoc, lift_snd, _root_.mul_assoc]
  rfl

theorem translPt_one : translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ 1) * snd T A = _
  rw [MonObj.comp_one, _root_.one_mul]

theorem translT_comp (x y : T ⟶ A) (h : y * x = 1) : translT A x ≫ translT A y = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, Category.id_comp]
    exact (congrArg (_ ≫ ·) (lift_snd _ _)).trans ((translT_translPt A x y).trans (h ▸ translPt_one A))

theorem isIso_translT_left (x : T ⟶ A) : IsIso (translT A x).left :=
  ⟨⟨(translT A x⁻¹).left, by rw [← Over.comp_left, translT_comp A _ _ (inv_mul_cancel x), Over.id_left],
    by rw [← Over.comp_left, translT_comp A _ _ (mul_inv_cancel x), Over.id_left]⟩⟩

end Transl

theorem geometric_fibre (hBC : PolBaseChangeSt)
    (hTW : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K]
      (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧
      ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left,
        (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen)
    {S : Scheme.{0}} (P : PolAV S) (q : ℕ) (hq : 1 ≤ q) {T : Over S} (c : T ⟶ P.A)
    (K : Type) [Field K] [IsAlgClosed K] (σ : Spec (CommRingCat.of K) ⟶ T.left) :
    ∃ (P' : PolAV (Spec (CommRingCat.of K))) (π : (baseOver _ ⊗ P'.A).left ⟶ (T ⊗ P.A).left), P'.g = P.g ∧
      IsPullback π (fst (baseOver _) P'.A).left (fst T P.A).left σ ∧
      LBIso (LPow P'.A P'.L q (baseOver _)) ((twistLB P.A P.L q c).pull π) := by
  obtain ⟨P', G, hG, hdim, hmul, w₀, hw₀⟩ := hBC S _ (σ ≫ T.hom) P
  let T' := baseOver (Spec (CommRingCat.of K))
  have hc : (σ ≫ c.left) ≫ P.A.hom = 𝟙 _ ≫ σ ≫ T.hom := by rw [Category.assoc, Over.w c, Category.id_comp]
  let c' : T' ⟶ P'.A := Over.homMk (hG.lift _ _ hc) (hG.lift_snd _ _ _)
  have hc' : c'.left ≫ G = σ ≫ c.left := hG.lift_fst _ _ _
  obtain ⟨d, -, w, hw⟩ := hTW _ P' K (𝟙 _) q hq c'
  have hf : (fst T' P'.A).left = (T' ⊗ P'.A).hom := (Category.comp_id _).symm.trans (Over.w (fst T' P'.A))
  let a : Over.mk ((T' ⊗ P'.A).hom ≫ σ ≫ T.hom) ⟶ T := Over.homMk ((fst T' P'.A).left ≫ σ) (by
    rw [hf]; exact Category.assoc _ _ _)
  let j := lift a (toBase hG.w (snd T' P'.A))
  have j₁ : j.left ≫ (fst T P.A).left = (fst T' P'.A).left ≫ σ :=
    congrArg (fun q => q.left) (lift_fst a (toBase hG.w (snd T' P'.A)))
  have j₂ : j.left ≫ (snd T P.A).left = (snd T' P'.A).left ≫ G :=
    congrArg (fun q => q.left) (lift_snd a (toBase hG.w (snd T' P'.A)))
  have j₃ : j.left ≫ (translPt P.A c).left = (translPt P'.A c').left ≫ G := by
    have e₁ : j ≫ translPt P.A c = (a ≫ c) * toBase hG.w (snd T' P'.A) := by
      show j ≫ ((fst T P.A ≫ c) * snd T P.A) = _
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    have e₂ : toBase hG.w (fst T' P'.A ≫ c') = a ≫ c := Over.OverMorphism.ext
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc').trans (Category.assoc _ _ _).symm))
    have e₃ := hmul _ (fst T' P'.A ≫ c') (snd T' P'.A)
    rw [e₂, ← e₁] at e₃
    exact (congrArg (fun q => q.left) e₃).symm
  have pj : IsPullback j.left (fst T' P'.A).left (fst T P.A).left σ := by
    refine IsPullback.of_right ?_ j₁ (IsPullback.of_hasPullback T.hom P.A.hom).flip
    have := (IsPullback.of_hasPullback T'.hom P'.A.hom).flip.paste_horiz hG
    refine (congrArg₂ (fun a b => IsPullback a (fst T' P'.A).left P.A.hom b) j₂ (Category.id_comp _).symm).mpr this
  let τ := (translT P'.A d⁻¹).left
  haveI : IsIso τ := isIso_translT_left P'.A d⁻¹
  have τ₁ : τ ≫ (fst T' P'.A).left = (fst T' P'.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : translT P'.A d⁻¹ ≫ _ = _)
  have τ₂ : (snd T' P'.A).left = τ ≫ (translPt P'.A d).left := by
    have := translT_translPt P'.A d⁻¹ d
    rw [mul_inv_cancel, translPt_one] at this
    exact (congrArg (fun q => q.left) this).symm
  refine ⟨P', τ ≫ j.left, hdim, ?_, ?_⟩
  · have : IsPullback τ (fst T' P'.A).left (fst T' P'.A).left (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨τ₁.trans (Category.comp_id _).symm⟩
    have := this.paste_horiz pj
    rwa [Category.id_comp] at this
  · obtain ⟨w₁, hw₁⟩ := LBIso.symm ⟨w₀, hw₀⟩
    have H := (iso_of_gen_three P'.L _ _ _ _ _ _ w hw).trans (LB.isLB_linComb P'.isLB _ _) (LB.isLB_linComb P'.isLB _ _)
      (LB.isLB_linComb P.isLB _ _) (iso_linComb ((isGen_iff w₁).1 hw₁) _ _)
    have H' := H.chartPull (chartPullSame P'.L (fun _ : Fin 1 => (snd T' P'.A).left) _ _ τ fun _ => τ₂)
      (chartPullSame P.L (fun k => (τ ≫ j.left) ≫ ![(snd T P.A).left, (translPt P.A c).left] k) _ _ τ fun k => by
        rw [Category.assoc]
        fin_cases k
        exacts [congrArg (τ ≫ ·) j₂, congrArg (τ ≫ ·) j₃])
    exact H'.chartPull (chartPullId _) (chartPullOut P.L _ _ _ _ fun _ => rfl)

theorem secTwist_of_perf : (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), 1 ≤ n → FirstCohomologyVanishes (pw P.L n)) → (∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e → M.IsLB → M'.IsLB → (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M') → (∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v) → PolBaseChangeSt → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left, (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen) → SecTwistSt := by
  intro hPerf hProj hVan hIso hMat hBC hH0 hTW S P q hq R _ _ t c
  let T : Over S := Over.mk t
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of R) := (fst T P.A).left
  have pb : IsPullback (snd T P.A).left f P.A.hom t := (IsPullback.of_hasPullback T.hom P.A.hom).flip
  have hM : (twistLB P.A P.L q c).IsLB := LB.isLB_linComb P.isLB _ _
  have hsm : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) pb P.isAb.smooth
  obtain ⟨N, -, m, s, hN, hs⟩ := hProj S P R t _ _ f pb
  obtain ⟨Q⟩ := hPerf R _ f hsm ⟨_, hN, m, s, hs⟩ _ hM
  let k := IsLocalRing.ResidueField R
  let K := AlgebraicClosure k
  let g₀ : R →+* K := (algebraMap k K).comp (IsLocalRing.residue R)
  obtain ⟨P', π, hdim, hπ, H⟩ := geometric_fibre hBC hTW P q hq c K (Spec.map (CommRingCat.ofHom g₀))
  have hL : (LPow P'.A P'.L q (baseOver _)).IsLB := LB.isLB_linComb P'.isLB _ _
  have hMπ := LB.isLB_pull hM π
  have h1 : FirstCohomologyVanishes ((twistLB P.A P.L q c).pull π) := by
    have : IsIso (snd (baseOver (Spec (CommRingCat.of K))) P'.A).left :=
      (IsPullback.of_hasPullback (𝟙 _) P'.A.hom).isIso_snd_of_isIso
    refine hIso _ _ (snd (baseOver _) P'.A).left _ _ this (isLB_pw P'.isLB q) hMπ ?_ (hVan K P' q hq)
    exact H.symm.trans hMπ hL (LB.isLB_pull (isLB_pw P'.isLB q) _)
      ((lbIso_refl (isLB_pw P'.isLB q)).chartPull (chartPullPw _ _ _) (chartPullPull _ _ _ rfl))
  obtain ⟨r, n, B, hr, hB, hu⟩ := hMat R K g₀ _ _ _ Q.D₀ Q.D₁ Q.comp (Q.exact K g₀ _ π _ hπ h1)
  have hru : IsUnit r := by
    by_contra h
    exact hr (by
      show algebraMap k K (IsLocalRing.residue R r) = 0
      rw [(IsLocalRing.residue_eq_zero_iff r).2 h, map_zero])
  have hn : n = q ^ P.g := by
    obtain ⟨b, hb⟩ := perf_bas Q g₀ hπ B hB (hu K g₀ (hru.map _))
    obtain ⟨b', hb'⟩ := hb.of_iso hMπ hL H.symm
    haveI : Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    rw [← finrank_of_isSecBasis P'.A P'.L q _ b' hb'.exists_unique, ← hdim]
    exact hH0 _ P' K (𝟙 _) q hq
  subst hn
  refine ⟨?_, fun sbar => ?_⟩
  · have h₀ : IsPullback (𝟙 _) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
      rw [CommRingCat.ofHom_id, Spec.map_id]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    obtain ⟨b, hb⟩ := perf_bas Q (RingHom.id R) h₀ B hB (hu R _ hru)
    obtain ⟨b', hb'⟩ := hb.of_iso (LB.isLB_pull hM _) hM
      ((lbIso_refl hM).chartPull (chartPullPull _ _ _ rfl) (chartPullId _))
    exact ⟨b', hb'.exists_unique⟩
  · let ρ : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ t) ⟶ T :=
      Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) rfl
    have hρ : IsPullback (ρ ▷ P.A).left (fst _ P.A).left f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := by
      refine IsPullback.of_right ?_ (congrArg (fun q => q.left) (whiskerRight_fst ρ P.A)) pb
      exact (congrArg (fun a => IsPullback a _ P.A.hom _)
        (congrArg (fun q => q.left) (whiskerRight_snd ρ P.A))).mpr (IsPullback.of_hasPullback _ P.A.hom).flip
    exact perf_lift P.L _ _ Q _ IsLocalRing.residue_surjective hρ B hB (hu _ _ (hru.map _)) sbar

end GlobalTheory.SecTwist
