import Formalism.LocalToGlobal.ProjectiveLattices.TieReadingOf
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def evCH (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (Z : Comp (T.Q.Xo j) T.Q.c) :
    T.R j →+* Om Z where
  toFun f := evC hG Z f
  map_one' := evalAt_one (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) _
    (h.allTest j hj (Om Z) _)
  map_mul' f g := evalAt_mul (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f g _
  map_zero' := evalAt_zero (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) _
  map_add' f g := evalAt_add (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f g _

theorem rdU_one_of (h : LawsP T) {j : ℕ} (hj : InR D j) (k : (T.U j T.σ₀).Comp)
    {y : Frame ((T.U j T.σ₀).X k).Ψ D.R.r} (hy : y ∈ ((T.U j T.σ₀).X k).dom) : rdU (T.U j T.σ₀) 1 k y = 1 := by
  haveI : IsReduced (CAt T.σ₀) := inferInstanceAs (IsReduced ℂ)
  unfold rdU
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
  show toC (evalAt (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) 1
    ((T.U j T.σ₀).un k ⟨y, hy⟩)) = 1
  rw [evalAt_one (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) _
    (h.allTest j hj _ _)]
  rfl

open Classical in

def frAt {j : ℕ} {k : (T.U j T.σ₀).Comp} (x₀ x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) :
    Frame ((T.U j T.σ₀).X k).Ψ D.R.r :=
  if x ∈ ((T.U j T.σ₀).X k).dom then x else x₀

theorem frAt_of_mem {j : ℕ} {k : (T.U j T.σ₀).Comp} (x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r)
    {x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r} (hx : x ∈ ((T.U j T.σ₀).X k).dom) : frAt x₀ x = x := by
  unfold frAt
  rw [if_pos hx]

theorem frAt_mem {j : ℕ} {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) (x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) :
    frAt x₀ x ∈ ((T.U j T.σ₀).X k).dom := by
  unfold frAt
  split_ifs with hx
  · exact hx
  · exact hx0

def evFr (h : LawsP T) {j : ℕ} (hj : InR D j) {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) : T.R j →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) where
  toFun f x := rdU (T.U j T.σ₀) f k (frAt x₀ x)
  map_one' := funext fun x => rdU_one_of h hj k (frAt_mem hx0 x)
  map_mul' f g := funext fun x => by
    show rdU (T.U j T.σ₀) (f * g) k (frAt x₀ x) = rdU (T.U j T.σ₀) f k (frAt x₀ x) * rdU (T.U j T.σ₀) g k (frAt x₀ x)
    rw [rdU_mul]; rfl
  map_zero' := funext fun x => by simp
  map_add' f g := funext fun x => by simp

theorem evFr_of_mem (h : LawsP T) {j : ℕ} (hj : InR D j) {k : (T.U j T.σ₀).Comp}
    {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r} (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) (f : T.R j)
    {x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r} (hx : x ∈ ((T.U j T.σ₀).X k).dom) :
    evFr h hj hx0 f x = rdU (T.U j T.σ₀) f k x := by
  show rdU (T.U j T.σ₀) f k (frAt x₀ x) = _
  rw [frAt_of_mem x₀ hx]

def augF {j : ℕ} (k : (T.U j T.σ₀).Comp) :
    AddMonoidAlgebra (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) (WTZ D.host.E) →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id _) 1 (fun _ _ => Commute.all _ _)

def thR (h : LawsP T) {j : ℕ} (hj : InR D j) {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) :
    AddMonoidAlgebra (T.R j) (WTZ D.host.E) →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  (augF k).comp (AddMonoidAlgebra.mapRingHom (WTZ D.host.E) (evFr h hj hx0))

theorem thR_single (h : LawsP T) {j : ℕ} (hj : InR D j) {k : (T.U j T.σ₀).Comp}
    {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r} (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) (G : WTZ D.host.E) (f : T.R j) :
    thR h hj hx0 (AddMonoidAlgebra.single G f) = evFr h hj hx0 f := by
  simp [thR, augF, AddMonoidAlgebra.liftNCRingHom]

def PsiZ (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (Z : Comp (T.Q.Xo j) T.Q.c) :
    AddMonoidAlgebra (T.R j) (WTZ D.host.E) →+* AC Z :=
  AddMonoidAlgebra.mapRingHom (WTZ D.host.E) (evCH h hj hG Z)

theorem PsiZ_single (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (Z : Comp (T.Q.Xo j) T.Q.c)
    (G : WTZ D.host.E) (f : T.R j) :
    PsiZ h hj hG Z (AddMonoidAlgebra.single G f) = AddMonoidAlgebra.single G (evC hG Z f) := by
  simp [PsiZ]
  rfl

theorem coeff_PsiZ (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (Z : Comp (T.Q.Xo j) T.Q.c)
    (b : AddMonoidAlgebra (T.R j) (WTZ D.host.E)) (G : WTZ D.host.E) :
    (PsiZ h hj hG Z b).coeff G = evC hG Z (b.coeff G) := by
  rfl

def gensR (h : LawsP T) (j : ℕ) : Set (AddMonoidAlgebra (T.R j) (WTZ D.host.E)) :=
  {b | ∃ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), b = AddMonoidAlgebra.single (wtZ (wtA u) u.n) F.1}

def secZ (T : Top D) (j : ℕ) (G : WTZ D.host.E) : Submodule T.Q.c.F (T.R j) :=
  ⨆ u : {u : WeightFamilies.Wt D j // wtZ (wtA u) u.n = G}, sec (T.Q.Xo j) T.Q.c (wtA u.1) u.1.n

theorem wtZ_inj {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} {n n' : ℕ} (e : wtZ a n = wtZ a' n') : a = a' ∧ n = n' := by
  simp only [wtZ, Prod.mk.injEq] at e
  obtain ⟨h1, h2⟩ := e
  refine ⟨funext fun x => ?_, by exact_mod_cast h2⟩
  have hx := congrFun h1 x
  exact_mod_cast hx

theorem secZ_cases {j : ℕ} {G : WTZ D.host.E} {f : T.R j} (hf : f ∈ secZ T j G) :
    f = 0 ∨ ∃ u : WeightFamilies.Wt D j, wtZ (wtA u) u.n = G ∧ f ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n := by
  by_cases hne : Nonempty {u : WeightFamilies.Wt D j // wtZ (wtA u) u.n = G}
  · obtain ⟨⟨u0, hu0⟩⟩ := hne
    right
    refine ⟨u0, hu0, ?_⟩
    have hle : secZ T j G ≤ sec (T.Q.Xo j) T.Q.c (wtA u0) u0.n := by
      refine iSup_le fun u => ?_
      obtain ⟨ha, hn⟩ := wtZ_inj (u.2.trans hu0.symm)
      rw [ha, hn]
    exact hle hf
  · left
    haveI : IsEmpty {u : WeightFamilies.Wt D j // wtZ (wtA u) u.n = G} := not_nonempty_iff.mp hne
    have hbot : secZ T j G = ⊥ := iSup_of_empty _
    rw [hbot] at hf
    exact (Submodule.mem_bot _).mp hf

theorem secZ_mul {j : ℕ} {G G' : WTZ D.host.E} {f g : T.R j} (hf : f ∈ secZ T j G) (hg : g ∈ secZ T j G') :
    f * g ∈ secZ T j (G + G') := by
  refine Submodule.iSup_induction _ (motive := fun f => f * g ∈ secZ T j (G + G')) hf (fun p f hf => ?_)
    (by rw [zero_mul]; exact zero_mem _) (fun f1 f2 h1 h2 => by rw [add_mul]; exact add_mem h1 h2)
  refine Submodule.iSup_induction _ (motive := fun g => f * g ∈ secZ T j (G + G')) hg (fun q g hg => ?_)
    (by rw [mul_zero]; exact zero_mem _) (fun g1 g2 h1 h2 => by rw [mul_add]; exact add_mem h1 h2)
  have hs := sec_mul (T.Q.Xo j) T.Q.c _ _ _ _ hf hg
  rw [← wtA_wadd] at hs
  refine Submodule.mem_iSup_of_mem ⟨WeightAlgebra.wadd p.1 q.1, ?_⟩ hs
  show wtZ (wtA (WeightAlgebra.wadd p.1 q.1)) (p.1.n + q.1.n) = G + G'
  rw [wtA_wadd, wtZ_add, p.2, q.2]

def w00 (D : D7) (j : ℕ) : WeightFamilies.Wt D j := WeightAlgebra.wscalar D j 0 ⟨0, rfl⟩

theorem zero_weight_algebraic_part {j : ℕ} : wtA (w00 D j) = 0 := by
  funext x
  simp [wtA, w00, WeightAlgebra.wscalar, ext0]

theorem one_mem_sec {j : ℕ} : (1 : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA (w00 D j)) (w00 D j).n := by
  rw [zero_weight_algebraic_part]
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1; rw [map_one]
  · show (1 : p.R) = wchar (ex (T.Q.Dw j) 0 0) t * 1
    have : ex (T.Q.Dw j) 0 0 = 0 := by funext i; cases i <;> rfl
    simp [wchar, this]

theorem zero_weight_exponent_zero {j : ℕ} : wtZ (wtA (w00 D j)) (w00 D j).n = 0 := by
  rw [zero_weight_algebraic_part]
  rfl

def secSub (T : Top D) (j : ℕ) : Subring (AddMonoidAlgebra (T.R j) (WTZ D.host.E)) where
  carrier := {b | ∀ G, b.coeff G ∈ secZ T j G}
  one_mem' G := by
    classical
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with hG0
    · subst hG0
      exact Submodule.mem_iSup_of_mem ⟨w00 D j, zero_weight_exponent_zero⟩ one_mem_sec
    · exact zero_mem _
  mul_mem' {a b} ha hb G := by
    classical
    rw [AddMonoidAlgebra.coeff_mul]
    refine Submodule.finsuppSum_mem _ _ _ _ fun m1 _ => Submodule.finsuppSum_mem _ _ _ _ fun m2 _ => ?_
    split_ifs with hm
    · subst hm; exact secZ_mul (ha m1) (hb m2)
    · exact zero_mem _
  zero_mem' G := by simp
  add_mem' {a b} ha hb G := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact add_mem (ha G) (hb G)
  neg_mem' {a} ha G := by
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]; exact neg_mem (ha G)

theorem single_mem_secSub {j : ℕ} {G : WTZ D.host.E} {g : T.R j} (hg : g ∈ secZ T j G) :
    AddMonoidAlgebra.single G g ∈ secSub T j := by
  classical
  show ∀ G', (AddMonoidAlgebra.single G g).coeff G' ∈ secZ T j G'
  intro G'
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with hG
  · subst hG
    exact hg
  · exact zero_mem _

theorem closure_le_secSub (h : LawsP T) (j : ℕ) : Subring.closure (gensR h j) ≤ secSub T j := by
  rw [Subring.closure_le]
  rintro b ⟨u, F, rfl⟩
  exact single_mem_secSub (Submodule.mem_iSup_of_mem ⟨u, rfl⟩ (cusp_le_sec _ _ _ _ _ (cutR_le T.C j u F.2)))

section Kappa
variable (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp} (hκ : KappaTie j hG κ) (Z : Comp (T.Q.Xo j) T.Q.c)

include h hj hκ in

theorem dom_ne : ((T.U j T.σ₀).X (κ Z)).dom.Nonempty := by
  by_contra hne
  have h1 := (hκ Z (w00 D j) 1 one_mem_sec).mpr (fun x hx => absurd ⟨x, hx⟩ hne)
  have h2 : evC hG Z (1 : T.R j) = 1 := (evCH h hj hG Z).map_one
  rw [h2] at h1
  exact one_ne_zero h1

variable {x₀ : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r} (hx0 : x₀ ∈ ((T.U j T.σ₀).X (κ Z)).dom)

include hκ in
theorem thR_eq_zero (b : AddMonoidAlgebra (T.R j) (WTZ D.host.E)) (hbS : b ∈ secSub T j)
    (hb : PsiZ h hj hG Z b = 0) : thR h hj hx0 b = 0 := by
  have hc : ∀ G, evFr h hj hx0 (b.coeff G) = 0 := by
    intro G
    have hG0 : evC hG Z (b.coeff G) = 0 := by
      rw [← coeff_PsiZ h hj hG Z b G, hb]
      rfl
    rcases secZ_cases (hbS G) with h0 | ⟨u, -, hu⟩
    · rw [h0, map_zero]
    · funext x
      exact (hκ Z u _ hu).mp hG0 (frAt x₀ x) (frAt_mem hx0 x)
  have hm : AddMonoidAlgebra.mapRingHom (WTZ D.host.E) (evFr h hj hx0) b = 0 := by
    first
    | (ext G x; exact congrFun (hc G) x)
    | (ext G : 1; exact hc G)
    | (ext G : 1; rw [AddMonoidAlgebra.coeff_zero]; exact hc G)
  show augF (κ Z) (AddMonoidAlgebra.mapRingHom (WTZ D.host.E) (evFr h hj hx0) b) = 0
  rw [hm, map_zero]

include hκ in
theorem thR_homog (b : AddMonoidAlgebra (T.R j) (WTZ D.host.E)) (hbS : b ∈ secSub T j) {G : WTZ D.host.E}
    (hb : PsiZ h hj hG Z b ∈ AG Z G) : thR h hj hx0 b = evFr h hj hx0 (b.coeff G) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  have h1 : PsiZ h hj hG Z b = AddMonoidAlgebra.single G c := by
    rw [← hc, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  have h2 : c = evC hG Z (b.coeff G) := by
    rw [← coeff_PsiZ h hj hG Z b G, h1, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have hS : AddMonoidAlgebra.single G (b.coeff G) ∈ secSub T j := single_mem_secSub (hbS G)
  have h3 : PsiZ h hj hG Z (b - AddMonoidAlgebra.single G (b.coeff G)) = 0 := by
    rw [map_sub, PsiZ_single, h1, h2, sub_self]
  have h4 := thR_eq_zero h hj hG hκ Z hx0 _ (sub_mem hbS hS) h3
  rw [map_sub, thR_single, sub_eq_zero] at h4
  exact h4
end Kappa

theorem isSec_zero' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) :
    X.IsSec la 0 := by
  refine ⟨differentiableOn_const _, fun x _ b _ => ?_, fun γ _ x _ => ?_⟩ <;> simp

theorem isSec_congr' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {la : Wt X.Ψ r}
    {P Q : Frame X.Ψ r → ℂ} (hPQ : ∀ x ∈ X.dom, P x = Q x) (hP : X.IsSec la P) : X.IsSec la Q := by
  unfold Data.IsSec at hP ⊢
  refine ⟨hP.1.congr fun x hx => (hPQ x hx).symm, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · rw [← hPQ _ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb), ← hPQ x hx]; exact hP.2.1 x hx b hb
  · rw [← hPQ _ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X hγ hx), ← hPQ x hx]; exact hP.2.2 γ hγ x hx

def weR (E : Type) [Field E] : AddSubgroup (WTZ E) where
  carrier := {G | Even G.2}
  add_mem' ha hb := Even.add ha hb
  zero_mem' := ⟨0, rfl⟩
  neg_mem' ha := Even.neg ha

def wtF {j : ℕ} (k : (T.U j T.σ₀).Comp) (G : WTZ D.host.E) : Wt ((T.U j T.σ₀).X k).Ψ D.R.r :=
  fun τ i => if ((T.U j T.σ₀).X k).p0 ≤ (i : ℕ) then
      G.1 (Function.invFun (relab T.Q.c T.σ₀) τ.1, (i : ℕ) - ((T.U j T.σ₀).X k).p0) + G.2 / 2
    else -G.1 (Function.invFun (relab T.Q.c T.σ₀) (conjEmb τ.1), ((T.U j T.σ₀).X k).p0 - 1 - (i : ℕ)) - G.2 / 2

theorem wtF_wtZ {j : ℕ} (k : (T.U j T.σ₀).Comp) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    wtF k (wtZ a n) = laU (T.U j T.σ₀) a n k := by
  funext τ i
  simp only [wtF, laU, wtZ]
  split_ifs <;> push_cast <;> rfl

def wtR {j : ℕ} (k : (T.U j T.σ₀).Comp) : weR D.host.E →+ Wt ((T.U j T.σ₀).X k).Ψ D.R.r where
  toFun G := wtF k G.1
  map_zero' := by funext τ i; simp [wtF]
  map_add' G G' := by
    funext τ i
    obtain ⟨a, ha⟩ := G.2
    obtain ⟨b, hb⟩ := G'.2
    simp only [wtF, AddSubgroup.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> omega

abbrev BcR (h : LawsP T) (j : ℕ) : Subring (AddMonoidAlgebra (T.R j) (WTZ D.host.E)) := Subring.closure (gensR h j)

def PsiC (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (Z : Comp (T.Q.Xo j) T.Q.c) :
    BcR h j →+* AC Z :=
  (PsiZ h hj hG Z).comp (BcR h j).subtype

def RgR (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (Z : Comp (T.Q.Xo j) T.Q.c) :
    Subring (AC Z) :=
  (PsiC h hj hG Z).range

section Rd
variable (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp} (hκ : KappaTie j hG κ) (Z : Comp (T.Q.Xo j) T.Q.c)
  {x₀ : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r} (hx0 : x₀ ∈ ((T.U j T.σ₀).X (κ Z)).dom)

def preR (f : RgR h hj hG Z) : BcR h j := (RingHom.mem_range.1 f.2).choose

theorem preR_spec (f : RgR h hj hG Z) : PsiC h hj hG Z (preR h hj hG Z f) = f.1 :=
  (RingHom.mem_range.1 f.2).choose_spec

include hκ in
theorem thR_congr (b b' : BcR h j) (e : PsiC h hj hG Z b = PsiC h hj hG Z b') : thR h hj hx0 b.1 = thR h hj hx0 b'.1 := by
  have hsub : b.1 - b'.1 ∈ secSub T j :=
    sub_mem (closure_le_secSub h j b.2) (closure_le_secSub h j b'.2)
  have h0 : PsiZ h hj hG Z (b.1 - b'.1) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr e
  have h1 := thR_eq_zero h hj hG hκ Z hx0 (b.1 - b'.1) hsub h0
  rw [map_sub, sub_eq_zero] at h1
  exact h1

set_option maxHeartbeats 1000000 in

def rdRg : RgR h hj hG Z →+* (Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r → ℂ) where
  toFun f := thR h hj hx0 (preR h hj hG Z f).1
  map_one' := (thR_congr h hj hG hκ Z hx0 _ 1 (by rw [preR_spec, map_one]; rfl)).trans (map_one _)
  map_mul' f g := (thR_congr h hj hG hκ Z hx0 _ (preR h hj hG Z f * preR h hj hG Z g)
    (by rw [map_mul, preR_spec, preR_spec, preR_spec]; rfl)).trans (map_mul _ _ _)
  map_zero' := by
    refine (thR_congr h hj hG hκ Z hx0 _ 0 ?_).trans ?_
    · rw [preR_spec, map_zero]; exact ZeroMemClass.coe_zero _
    · rw [ZeroMemClass.coe_zero, map_zero]
  map_add' f g := by
    refine (thR_congr h hj hG hκ Z hx0 _ (preR h hj hG Z f + preR h hj hG Z g) ?_).trans ?_
    · rw [map_add, preR_spec, preR_spec, preR_spec]; exact Subring.coe_add _ f g
    · rw [Subring.coe_add, map_add]

theorem rdRg_apply (b : BcR h j) (hb : PsiC h hj hG Z b ∈ RgR h hj hG Z) :
    rdRg h hj hG hκ Z hx0 ⟨PsiC h hj hG Z b, hb⟩ = thR h hj hx0 b.1 :=
  thR_congr h hj hG hκ Z hx0 _ b (preR_spec h hj hG Z _)

theorem rd_homog {G : WTZ D.host.E} {f : AC Z} (hf : f ∈ RgR h hj hG Z) (hfA : f ∈ AG Z G) :
    ∃ g ∈ secZ T j G, rdRg h hj hG hκ Z hx0 ⟨f, hf⟩ = evFr h hj hx0 g ∧
      f = AddMonoidAlgebra.single G (evC hG Z g) := by
  have hPb : PsiZ h hj hG Z (preR h hj hG Z ⟨f, hf⟩).1 = f := preR_spec h hj hG Z ⟨f, hf⟩
  have hbS : (preR h hj hG Z ⟨f, hf⟩).1 ∈ secSub T j := closure_le_secSub h j (preR h hj hG Z ⟨f, hf⟩).2
  refine ⟨(preR h hj hG Z ⟨f, hf⟩).1.coeff G, hbS G, ?_, ?_⟩
  · show thR h hj hx0 (preR h hj hG Z ⟨f, hf⟩).1 = _
    exact thR_homog h hj hG hκ Z hx0 _ hbS (by rw [hPb]; exact hfA)
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfA
    have h1 : f = AddMonoidAlgebra.single G c := by
      rw [← hc, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    have h2 : f.coeff G = evC hG Z ((preR h hj hG Z ⟨f, hf⟩).1.coeff G) := by
      rw [← coeff_PsiZ h hj hG Z, hPb]
    have h3 : c = evC hG Z ((preR h hj hG Z ⟨f, hf⟩).1.coeff G) := by
      rw [← h2, h1, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    rw [h3] at h1
    exact h1

theorem valC_mem_Rg (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) :
    valC hG (wtA u) u.n F.1 Z ∈ RgR h hj hG Z := by
  refine ⟨⟨AddMonoidAlgebra.single (wtZ (wtA u) u.n) F.1, Subring.subset_closure ⟨u, F, rfl⟩⟩, ?_⟩
  show PsiZ h hj hG Z (AddMonoidAlgebra.single (wtZ (wtA u) u.n) F.1) = _
  rw [PsiZ_single]
  rfl
end Rd

def rdData1 (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    {κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp} (hκ : KappaTie j hG κ) (hd : DTie h j hG d)
    (Z : Comp (T.Q.Xo j) T.Q.c) : RdData1 d Z ((T.U j T.σ₀).X (κ Z)) where
  Rg := RgR h hj hG Z
  w_mem i := by
    obtain ⟨uL, W, -, -, hw⟩ := hd
    rw [hw.1 i Z]; exact valC_mem_Rg h hj hG Z uL (W i)
  rd := rdRg h hj hG hκ Z (dom_ne h hj hG hκ Z).some_mem
  WE := weR D.host.E
  wL_mem := by
    obtain ⟨uL, W, hev, hwL, -⟩ := hd
    rw [hwL]; show Even ((uL.n : ℕ) : ℤ); exact_mod_cast hev
  wt := wtR (κ Z)

theorem tieRd1 (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    {κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp} (hκ : KappaTie j hG κ) (hd : DTie h j hG d)
    (Z : Comp (T.Q.Xo j) T.Q.c) : TieRd1Props h hG d κ Z (rdData1 h hj hG d hκ hd Z) := by
  have hx0 := (dom_ne h hj hG hκ Z).some_mem
  refine ⟨fun G hGE f hf hfA => ?_, fun G f hf hfA hz => ?_, fun u F _ => valC_mem_Rg h hj hG Z u F,
    fun u hu => (show Even ((u.n : ℕ) : ℤ) by exact_mod_cast hu),
    fun u F hF x hx => ?_, fun u hu => wtF_wtZ (κ Z) (wtA u) u.n⟩
  · obtain ⟨g, hg, hrd, -⟩ := rd_homog h hj hG hκ Z hx0 hf hfA
    show ((T.U j T.σ₀).X (κ Z)).IsSec (wtF (κ Z) G) (rdRg h hj hG hκ Z hx0 ⟨f, hf⟩)
    rw [hrd]
    rcases secZ_cases hg with rfl | ⟨u, rfl, hs⟩
    · rw [map_zero]; exact isSec_zero' _ _
    · rw [wtF_wtZ]
      exact isSec_congr' _ (fun x hx => (evFr_of_mem h hj hx0 g hx).symm)
        ((h.unf j hj T.σ₀ T.good_σ₀).2.2.2.2.1 (wtA u) u.n (dom_wtA u) g hs (κ Z))
  · obtain ⟨g, hg, hrd, hfe⟩ := rd_homog h hj hG hκ Z hx0 hf hfA
    have hv : ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, rdU (T.U j T.σ₀) g (κ Z) x = 0 := fun x hx => by
      rw [← evFr_of_mem h hj hx0 g hx, ← hrd]; exact hz x hx
    have he : evC hG Z g = 0 := by
      rcases secZ_cases hg with rfl | ⟨u, -, hs⟩
      · exact (evCH h hj hG Z).map_zero
      · exact (hκ Z u g hs).2 hv
    rw [hfe, he, AddMonoidAlgebra.single_zero]
  · have hb0 : PsiC h hj hG Z ⟨_, Subring.subset_closure ⟨u, F, rfl⟩⟩ = valC hG (wtA u) u.n F.1 Z :=
      PsiZ_single h hj hG Z _ F.1
    have e : (⟨valC hG (wtA u) u.n F.1 Z, hF⟩ : RgR h hj hG Z) =
        ⟨PsiC h hj hG Z ⟨_, Subring.subset_closure ⟨u, F, rfl⟩⟩, by rw [hb0]; exact hF⟩ := Subtype.ext hb0.symm
    show rdRg h hj hG hκ Z hx0 ⟨_, hF⟩ x = _
    rw [e, rdRg_apply, thR_single, evFr_of_mem h hj hx0 _ hx]
    rfl

end Formalism.L2.Pj
