import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RedPullPd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Same
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PullRId

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.H2

open Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {Y : CB l K}

open Classical in

def coL {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) : HG (L.QB M) r j →+ ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l] :=
  if h : ∃ co, IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j co then h.choose else 0

theorem isCo (hC : CoEx l K) {m : ℕ} (L : Lv Y m) {M : Model l K} (hM : M.Sm) {r : ℕ} (j : ℕ) (h : r < m) :
    IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j (coL L M r j) := by
  rw [coL, dif_pos (hC L M hM r j h).2]
  exact (hC L M hM r j h).2.choose_spec

theorem aCo (hC : CoEx l K) {m : ℕ} (L : Lv Y m) {M : Model l K} (hM : M.Sm) {r : ℕ} (j : ℕ) (h : r < m) :
    ACo (V := fun a => Hdg M.q a j) L.θ (fun a => L.μ M a r j) r (coL L M r j) :=
  ⟨(isCo hC L hM j h).smul, (isCo hC L hM j h).same, (isCo hC L hM j h).diff, (hC L M hM r j h).1⟩

def idH {m : ℕ} (L : Lv Y m) : LHom L L (RingHom.id _) (fun _ => RingHom.id _) (RingHom.id _) 1 where
  le := le_rfl
  sA := RingHom.id _
  sB := RingHom.id _
  dpA := (DPMorphism.id L.γ).isDPMorphism
  dpB := (DPMorphism.id L.γB).isDPMorphism
  oA _ := rfl
  oB _ := rfl
  ι _ := rfl
  lam _ := rfl
  cris _ _ := rfl
  θ _ := rfl
  cB := 1
  t := (one_mul _).symm
  θc := map_one _

theorem co_hom (hC : CoEx l K) (hμ : HomMu l K) {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
    {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K} (hM : M.Sm) (hN : N.Sm)
    (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r : ℕ} (j : ℕ) (hr : r < m') (w : HG (L.QB N) r j) (a : ℕ)
    (φ : Module.Dual K (Hdg M.q a j)) :
    coL L' M r j (h.fW u hu r j w) a φ =
      c ^ (r - a) * sC (coL L N r j w a (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a j)) := by
  have := (aCo hC L hN j (hr.trans_le h.le)).hom (aCo hC L' hM j hr) le_rfl sC h.θ h.oB (h.fW u hu r j)
    (fun a => pullH (Model.genMap u hu) (Model.genMap_q u hu) a j) (fun a => h.cB ^ (r - a)) (fun a _ y => hμ h u hu a r j y) w a φ
  rw [map_pow, h.θc] at this
  exact this

def pullM (Y : CB l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) :
    GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (RingHom.id _) :=
  B.crMor (F := B.schFn N.p) (F' := B.schFn M.p) (b := Y.bs n) (b' := Y.bs n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl

theorem comp_id (hF : KForm) (M : Model l K) (h : 𝟙 M.X ≫ M.p = M.p) (a j : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    φ ∘ₗ pullH (Model.genMap (𝟙 M.X) h) (Model.genMap_q _ h) a j = φ :=
  LinearMap.ext fun x => congrArg φ (hF.pull_id M.q _ _ (genMap_id M h) a j x)

theorem down (hC : CoEx l K) (hR : HomRho l K) (hμ : HomMu l K) (hF : KForm) {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'}
    (h : LHom L L' (RingHom.id _) (fun _ => RingHom.id _) (RingHom.id _) 1) {M : Model l K} (hM : M.Sm) {r j : ℕ} (hr : r < m')
    (x : Y.Fam M r j) (w : HG (L.QB M) r j) (hw : L.Rho x w) : ∃ w', L'.Rho x w' ∧ coL L' M r j w' = coL L M r j w := by
  have h1 := hR h (𝟙 M.X) (Category.id_comp _) (pullM Y (𝟙 M.X) (Category.id_comp _)) (fun _ _ _ => rfl) r j x w hw
  have e : (fun n => (pdOm (pullM Y (𝟙 M.X) (Category.id_comp _) n) (RingHom.id _) (h.cris n) r).pull j (x n)) = x :=
    funext fun n => pd_id (pullM Y (𝟙 M.X) (Category.id_comp _) n) (h.cris n) (fun _ => rfl)
      (fun B₀ y => Category.comp_id (show Spec B₀ ⟶ M.X from y.1.2)) r j (x n)
  rw [e] at h1
  refine ⟨_, h1, funext fun a => AddMonoidHom.ext fun φ => ?_⟩
  rw [co_hom hC hμ h hM hM _ _ j hr, comp_id hF, one_pow, one_mul]; rfl

variable (S : ∀ m, Lv Y (m + 1))

open Classical in

def gam {M : Model l K} {r j : ℕ} (x : Y.Fam M r j) : ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l] :=
  if h : ∃ w, (S r).Rho x w then coL (S r) M r j h.choose else 0

variable {S}

structure Hyp (S : ∀ m, Lv Y (m + 1)) : Prop where
  ex : RhoEx l K
  co : CoEx l K
  hom : HomRho l K
  mu : HomMu l K
  mul : MulRho l K
  c1 : FirstChernHodgeTateCompat l K
  form : KForm
  dn : ∀ m, Nonempty (LHom (S (m + 1)) (S m) (RingHom.id _) (fun _ => RingHom.id _) (RingHom.id _) 1)

namespace Hyp
variable (H : Hyp S) {M : Model l K} (hM : M.Sm)
include H hM

theorem gam_eq {r j m : ℕ} (hm : r ≤ m) {x : Y.Fam M r j} (hx : CB.Comp x) {w : HG ((S m).QB M) r j} (hw : (S m).Rho x w) :
    gam S x = coL (S m) M r j w := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [gam, dif_pos ⟨w, hw⟩]
    exact congrArg _ ((H.ex.ex (S r) M hM r j r.lt_succ_self x hx).unique (Exists.choose_spec ⟨w, hw⟩) hw)
  | succ m hm ih =>
    obtain ⟨w', h1, h2⟩ := down H.co H.hom H.mu H.form (H.dn m).some hM (Nat.lt_succ_of_le hm) x w hw
    exact (ih h1).trans h2

theorem rho {r j m : ℕ} (hm : r ≤ m) {x : Y.Fam M r j} (hx : CB.Comp x) : ∃ w, (S m).Rho x w :=
  (H.ex.ex (S m) M hM r j (Nat.lt_succ_of_le hm) x hx).exists

theorem add {r j : ℕ} {x y : Y.Fam M r j} (hx : CB.Comp x) (hy : CB.Comp y) (hxy : CB.Comp (x + y)) (a : ℕ) :
    gam S (x + y) a = gam S x a + gam S y a := by
  obtain ⟨w, hw⟩ := H.rho hM le_rfl hx
  obtain ⟨w', hw'⟩ := H.rho hM le_rfl hy
  rw [H.gam_eq hM le_rfl hxy (H.ex.add _ _ _ _ _ _ _ _ hw hw'), H.gam_eq hM le_rfl hx hw, H.gam_eq hM le_rfl hy hw', map_add]
  rfl

theorem lin {r j : ℕ} (c : Y.Λ) {x : Y.Fam M r j} (hx : CB.Comp x) (hc : CB.Comp (c • x)) (a : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    gam S (c • x) a φ = Y.θ c * gam S x a φ := by
  obtain ⟨w, hw⟩ := H.rho hM le_rfl hx
  rw [H.gam_eq hM le_rfl hc (H.ex.smul _ _ _ _ c _ _ hw), H.gam_eq hM le_rfl hx hw, ← (S r).θ_lam]
  exact (isCo H.co (S r) hM j r.lt_succ_self).smul _ _ _ _

theorem lin' {r j : ℕ} {x : Y.Fam M r j} (hx : CB.Comp x) (a : ℕ) (k : K) (φ : Module.Dual K (Hdg M.q a j)) :
    gam S x a (k • φ) = kC K k * gam S x a φ := by
  obtain ⟨w, hw⟩ := H.rho hM le_rfl hx
  rw [H.gam_eq hM le_rfl hx hw, ← (S r).θ_K]
  exact (isCo H.co (S r) hM j r.lt_succ_self).lin _ _ _ _

theorem big {r j : ℕ} {x : Y.Fam M r j} (hx : CB.Comp x) (a : ℕ) (ha : r < a) : gam S x a = 0 := by
  obtain ⟨w, hw⟩ := H.rho hM le_rfl hx
  rw [H.gam_eq hM le_rfl hx hw]
  exact (isCo H.co (S r) hM j r.lt_succ_self).big a ha w

set_option maxHeartbeats 1600000 in
theorem sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') {x : Y.Fam M r j} (hx : CB.Comp x) (hs : CB.Comp (CB.shS k h x)) (a : ℕ) :
    gam S (CB.shS k h x) a = gam S x a := by
  have hr : r ≤ r' := by omega
  obtain ⟨w, hw⟩ := H.rho hM hr hx
  rw [H.gam_eq hM le_rfl hs (H.mul.sh _ _ k h _ _ hw), H.gam_eq hM hr hx hw]
  refine AddMonoidHom.ext fun φ => ?_
  have := (aCo H.co (S r') hM j (Nat.lt_succ_of_le hr)).hom (aCo H.co (S r') hM j r'.lt_succ_self) hr (sB := RingHom.id _)
    (RingHom.id _) (fun _ => rfl) (fun _ => rfl) (shG ((S r').QB M) (S r').tB_mem k h j) (fun _ => LinearMap.id) (fun _ => 1)
    (fun a ha y => (H.mul.sh_μ _ _ k h a ha y).trans (one_smul _ _).symm) w a φ
  rw [map_one, one_mul] at this
  exact this

theorem hom' {N : Model l K} (hN : N.Sm) {sΛ : Y.Λ →+* Y.Λ} {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} {r j : ℕ}
    (h : LHom (S r) (S r) sΛ sn sC c) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)
    (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n))
    (hpt : ∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u)
    {x : Y.Fam N r j} (hx : CB.Comp x) (x' : Y.Fam M r j) (hx' : CB.Comp x')
    (hc : ∀ n a, sn n (Y.c n a) = Y.c n (sΛ a)) (e : ∀ n, x' n = (pdOm (mm n) sΛ (hc n) r).pull j (x n))
    (a : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    gam S x' a φ = c ^ (r - a) * sC (gam S x a (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a j)) := by
  obtain ⟨w, hw⟩ := H.rho hN le_rfl hx
  have h1 := H.hom h u hu mm hpt r j x w hw
  obtain rfl : x' = fun n => (pdOm (mm n) sΛ (h.cris n) r).pull j (x n) := funext e
  rw [H.gam_eq hM le_rfl hx' h1, H.gam_eq hN le_rfl hx hw]
  exact co_hom H.co H.mu h hM hN u hu j r.lt_succ_self w a φ

theorem nat {N : Model l K} (hN : N.Sm) {r j : ℕ} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)
    {x : Y.Fam N r j} (hx : CB.Comp x) (x' : Y.Fam M r j) (hx' : CB.Comp x')
    (e : ∀ n, x' n = (pdOm (c := Y.c n) (c' := Y.c n) (pullM Y u hu n) (RingHom.id Y.Λ) (fun _ => rfl) r).pull j (x n))
    (a : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    gam S x' a φ = gam S x a (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a j) := by
  rw [H.hom' hM hN (idH (S r)) u hu (pullM Y u hu) (fun _ _ _ => rfl) hx x' hx' (fun _ _ => rfl) e, one_pow, one_mul]; rfl

theorem gal {sΛ : Y.Λ →+* Y.Λ} {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} {r j : ℕ}
    (h : LHom (S r) (S r) sΛ sn sC c) (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L M n) (Y.L M n) (sn n))
    (hpt : ∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = y.1.2)
    {x : Y.Fam M r j} (hx : CB.Comp x) (x' : Y.Fam M r j) (hx' : CB.Comp x')
    (hc : ∀ n a, sn n (Y.c n a) = Y.c n (sΛ a)) (e : ∀ n, x' n = (pdOm (mm n) sΛ (hc n) r).pull j (x n))
    (a : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    c ^ a * gam S x' a φ = c ^ r * sC (gam S x a φ) := by
  rcases le_or_gt a r with ha | ha
  · rw [H.hom' hM hM h (𝟙 M.X) (Category.id_comp _) mm (fun n B₀ y => (hpt n B₀ y).trans (Category.comp_id _).symm) hx x' hx' hc e,
      comp_id H.form, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' ha]
  · rw [H.big hM hx a ha, H.big hM hx' a ha]; simp

theorem cup {r r' s i j : ℕ} (h : r + r' = s) {x : Y.Fam M r i} {y : Y.Fam M r' j} (hx : CB.Comp x) (hy : CB.Comp y)
    (hxy : CB.Comp (CB.cupS h x y)) {m m' : ℕ → ℕ} (b : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a i))
    (b' : ∀ a, Module.Basis (Fin (m' a)) K (Hdg M.q a j)) (c : ℕ) (φ : Module.Dual K (Hdg M.q c (i + j))) :
    gam S (CB.cupS h x y) c φ = ∑ p : (Finset.HasAntidiagonal.antidiagonal c : Finset (ℕ × ℕ)), ∑ s, ∑ s',
      gam S x p.1.1 ((b p.1.1).coord s) * gam S y p.1.2 ((b' p.1.2).coord s') *
        kC K (φ (cupH M.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl (b p.1.1 s) (b' p.1.2 s'))) := by
  have h1 : r ≤ s := by omega
  have h2 : r' ≤ s := by omega
  obtain ⟨w, hw⟩ := H.rho hM h1 hx
  obtain ⟨w', hw'⟩ := H.rho hM h2 hy
  obtain ⟨β, hβ⟩ := CrystallineSemistableComparison.P.cup_bilin (grOkQ ((S s).QB M) h).pair (rfl : i + j = i + j)
  rw [H.gam_eq hM le_rfl hxy (H.mul.cup _ _ h _ _ _ _ hw hw'), H.gam_eq hM h1 hx hw, H.gam_eq hM h2 hy hw']
  have := (aCo H.co (S s) hM i (Nat.lt_succ_of_le h1)).cup (aCo H.co (S s) hM j (Nat.lt_succ_of_le h2))
    (aCo H.co (S s) hM (i + j) s.lt_succ_self) h (kC K) (S s).θ_K β (fun e y y' => cupH M.q e rfl y y')
    (fun e => H.form.bilin M.q e rfl) (fun e ha ha' y y' => (hβ _ _).trans (H.mul.cup_μ _ _ h e ha ha' y y')) b b' c φ w w'
  rw [hβ] at this
  exact this

theorem one (h1 : CB.Comp (Y.oneS M)) (φ : Module.Dual K (Hdg M.q 0 0)) : gam S (Y.oneS M) 0 φ = kC K (φ (oneH M.q)) := by
  rw [H.gam_eq hM le_rfl h1 (H.mul.one (S 0) M), ← (S 0).θ_K]
  exact (isCo H.co (S 0) hM 0 Nat.one_pos).same 0 le_rfl _ _

theorem c1' (D : E.LineData M.X) (hD : sSup (𝒱D D) = ⊤) (x : Y.Fam M 1 2) (c : Hdg M.q 1 2) (hx : CB.Comp x) (h1 : CB.IsFirstChernClassInFamily D x)
    (h2 : IsDlogFirstChernClass M.q (genD D) c) : (∀ φ, gam S x 1 φ = kC K (φ c)) ∧ ∀ a, a ≠ 1 → gam S x a = 0 := by
  rw [H.gam_eq hM le_rfl hx (H.c1 (S 1) M Nat.one_lt_two D hD x c h1 h2)]
  exact ⟨fun φ => ((isCo H.co (S 1) hM 2 Nat.one_lt_two).same 1 le_rfl _ _).trans ((S 1).θ_K _),
    fun a ha => (isCo H.co (S 1) hM 2 Nat.one_lt_two).diff a 1 ha _⟩

end Hyp

end CrystallineSemistableComparison.HT.H2
