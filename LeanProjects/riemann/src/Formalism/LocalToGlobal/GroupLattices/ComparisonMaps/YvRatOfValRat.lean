import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
import Formalism.LocalRingCardinality.DataLatDefs

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions

section Gen

variable {LL Kf : Type} [Field LL] [Field Kf] (e : LL →+* Kf)

theorem exists_fun_ne {c : Kf} (hc : c ≠ 0) : ∃ π : Kf →+ LL, (∀ a x, π (e a * x) = a * π x) ∧ π c ≠ 0 := by
  letI : Module LL Kf := e.toModule
  have hne : ¬ ∀ φ : Module.Dual LL Kf, φ c = 0 := fun h => hc ((Module.forall_dual_apply_eq_zero_iff LL c).1 h)
  push_neg at hne
  obtain ⟨φ, hφ⟩ := hne
  exact ⟨φ.toAddMonoidHom, fun a x => φ.map_smul a x, hφ⟩

theorem exists_retr : ∃ π : Kf →+ LL, (∀ a x, π (e a * x) = a * π x) ∧ ∀ a, π (e a) = a := by
  obtain ⟨π, hπ, h1⟩ := exists_fun_ne e (one_ne_zero : (1 : Kf) ≠ 0)
  refine ⟨(AddMonoidHom.mulLeft (π 1)⁻¹).comp π, fun a x => ?_, fun a => ?_⟩
  · show (π 1)⁻¹ * π (e a * x) = a * ((π 1)⁻¹ * π x)
    rw [hπ]
    ring
  · show (π 1)⁻¹ * π (e a) = a
    have h2 := hπ a 1
    rw [mul_one] at h2
    rw [h2, mul_left_comm, inv_mul_cancel₀ h1, mul_one]

variable {V W T : Type} [AddCommGroup V] [Module LL V] [AddCommGroup W] [Module Kf W]
  (ev : T → W →ₗ[Kf] Kf) (cmp : V →+ W)

def IsRat (F : W) : Prop := ∀ t, ev t F ∈ Set.range e

theorem ev_pi (hsm : ∀ (a : LL) x, cmp (a • x) = e a • cmp x) (hval : ∀ x, IsRat e ev (cmp x))
    (π : Kf →+ LL) (hπ : ∀ a x, π (e a * x) = a * π x) (c : V →₀ Kf) (t : T) :
    ev t (cmp (c.sum fun x a => π a • x)) = e (π (ev t (c.sum fun x a => a • cmp x))) := by
  simp only [Finsupp.sum, map_sum, hsm, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨r, hr⟩ := hval x t
  rw [← hr, mul_comm (c x), hπ, map_mul, mul_comm]

theorem rat_mem (hsep : ∀ F : W, (∀ t, ev t F = 0) → F = 0)
    (hsm : ∀ (a : LL) x, cmp (a • x) = e a • cmp x) (hval : ∀ x, IsRat e ev (cmp x))
    {F : W} (hF : F ∈ Submodule.span Kf (Set.range cmp)) (hr : IsRat e ev F) : ∃ x, cmp x = F := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hF
  obtain ⟨π, hπ, hπe⟩ := exists_retr e
  refine ⟨c.sum fun x a => π a • x, sub_eq_zero.1 (hsep _ fun t => ?_)⟩
  rw [map_sub, ev_pi e ev cmp hsm hval π hπ c t, sub_eq_zero]
  obtain ⟨r, hr⟩ := hr t
  rw [← hr, hπe]

theorem li_of_rat (hsep : ∀ F : W, (∀ t, ev t F = 0) → F = 0)
    (hsm : ∀ (a : LL) x, cmp (a • x) = e a • cmp x) (hval : ∀ x, IsRat e ev (cmp x))
    (hinj : Function.Injective cmp) {ι : Type} (b : ι → V) (hb : LinearIndependent LL b) :
    LinearIndependent Kf fun a => cmp (b a) := by
  rw [linearIndependent_iff'] at hb ⊢
  intro s g hg i hi
  by_contra hgi
  obtain ⟨π, hπ, hπi⟩ := exists_fun_ne e hgi
  refine hπi (hb s (fun j => π (g j)) ?_ i hi)
  apply hinj
  rw [map_zero]
  apply hsep
  intro t
  have key : ∀ j, e (π (g j)) * ev t (cmp (b j)) = e (π (g j * ev t (cmp (b j)))) := by
    intro j
    obtain ⟨r, hr⟩ := hval (b j) t
    rw [← hr, mul_comm (g j), hπ, map_mul, mul_comm]
  have h0 := congrArg (fun F => e (π (ev t F))) hg
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h0
  simp only [map_sum, hsm, map_smul, smul_eq_mul, key]
  exact h0

def descOp (hsm : ∀ (a : LL) x, cmp (a • x) = e a • cmp x) (hinj : Function.Injective cmp) (Tp : W →ₗ[Kf] W)
    (h : ∀ x, ∃ y, cmp y = Tp (cmp x)) : V →ₗ[LL] V where
  toFun x := Classical.choose (h x)
  map_add' x y := by
    apply hinj
    have h1 := Classical.choose_spec (h (x + y))
    have h2 := Classical.choose_spec (h x)
    have h3 := Classical.choose_spec (h y)
    rw [map_add cmp (Classical.choose (h x)), h1, h2, h3, map_add, map_add]
  map_smul' a x := by
    apply hinj
    have h1 := Classical.choose_spec (h (a • x))
    have h2 := Classical.choose_spec (h x)
    rw [RingHom.id_apply, hsm a (Classical.choose (h x)), h1, h2, hsm, map_smul]

theorem descOp_spec (hsm : ∀ (a : LL) x, cmp (a • x) = e a • cmp x) (hinj : Function.Injective cmp) (Tp : W →ₗ[Kf] W)
    (h : ∀ x, ∃ y, cmp y = Tp (cmp x)) (x : V) : cmp (descOp e cmp hsm hinj Tp h x) = Tp (cmp x) := Classical.choose_spec (h x)

end Gen

section Pl

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (α : Type) {LL : Type} [Field LL] (e : LL →+* Kf)

abbrev FnP : Type := α → P.Tup → P.Xsp

def evP (t : α × P.Tup × ((Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) →₀ ℕ)) :
    FnP P α →ₗ[Kf] Kf :=
  (MvPolynomial.lcoeff Kf t.2.2) ∘ₗ (LinearMap.proj t.2.1) ∘ₗ (LinearMap.proj t.1)

theorem localComponent_apply₂ (i : α) (L : P.Tup) (m) (F : FnP P α) : evP P α (i, L, m) F = coeff m (F i L) := rfl

theorem eq_zero_of_forall_evalCoeff_eq_zero (F : FnP P α) (h : ∀ t, evP P α t F = 0) : F = 0 := by
  funext i L
  refine MvPolynomial.ext _ _ fun m => ?_
  have h1 := h (i, L, m)
  rw [localComponent_apply₂] at h1
  simpa using h1

def RatFnP (F : FnP P α) : Prop := ∀ i L, ∃ Q : MvPolynomial _ LL, MvPolynomial.map e Q = F i L

theorem isRational_iff (F : FnP P α) : RatFnP P α e F ↔ IsRat e (evP P α) F := by
  constructor
  · rintro h ⟨i, L, m⟩
    obtain ⟨Q, hQ⟩ := h i L
    rw [localComponent_apply₂, ← hQ, MvPolynomial.coeff_map]
    exact ⟨_, rfl⟩
  · intro h i L
    obtain ⟨π, -, hπe⟩ := exists_retr e
    have hc : ∀ n, e (π (coeff n (F i L))) = coeff n (F i L) := fun n => by
      obtain ⟨r, hr⟩ := h (i, L, n)
      rw [localComponent_apply₂] at hr
      rw [← hr, hπe]
    refine ⟨∑ n ∈ (F i L).support, MvPolynomial.monomial n (π (coeff n (F i L))), ?_⟩
    rw [map_sum]
    simp only [MvPolynomial.map_monomial, hc]
    exact (MvPolynomial.as_sum (F i L)).symm

end Pl

section Loc

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

abbrev evG := evP G.P G.comp

theorem evG_apply (i : G.comp) (L : G.P.Tup) (m) (F : G.Fn) : evG G (i, L, m) F = coeff m (F i L) := rfl

theorem evG_sep (F : G.Fn) (h : ∀ t, evG G t F = 0) : F = 0 := eq_zero_of_forall_evalCoeff_eq_zero G.P G.comp F h

abbrev RatFn (F : G.Fn) : Prop := RatFnP G.P G.comp e F

theorem ratFn_iff (F : G.Fn) : RatFn G e F ↔ IsRat e (evG G) F := isRational_iff G.P G.comp e F

def yK (v : Fin G.P.nV) : G.Fn →ₗ[G.Kf] G.Fn where
  toFun := G.yv v
  map_add' F F' := (LatticeSystems.yEnd G v).map_add F F'
  map_smul' c F := by
    funext i L
    show Level.yv (P := G.P) v ((c • F) i) L = c • Level.yv (P := G.P) v (F i) L
    rw [LatticeSystems.ef_yv_eq, LatticeSystems.ef_yv_eq, smul_comm c]
    congr 1
    rw [Finset.smul_sum]
    rfl

@[simp] theorem yK_apply (v : Fin G.P.nV) (F : G.Fn) : yK G v F = G.yv v F := rfl

theorem yv_rat (v : Fin G.P.nV) (F : G.Fn) (h : IsRat e (evG G) F) : IsRat e (evG G) (G.yv v F) := by
  rintro ⟨i, L, m⟩
  have hF : ∀ L', coeff m (F i L') ∈ e.range := fun L' => by
    obtain ⟨r, hr⟩ := h (i, L', m)
    exact RingHom.mem_range.2 ⟨r, hr.trans (evG_apply G i L' m F)⟩
  have hp : ((p : G.Kf) ^ G.P.ArV v) ∈ e.range := RingHom.mem_range.2 ⟨(p : LL) ^ G.P.ArV v, by simp⟩
  show coeff m (Level.yv (P := G.P) v (F i) L) ∈ Set.range e
  rw [LatticeSystems.ef_yv_eq, MvPolynomial.coeff_smul, MvPolynomial.coeff_sum, smul_eq_mul]
  exact RingHom.mem_range.1 (Subring.mul_mem _ hp (Subring.sum_mem _ fun L'' _ => hF _))

theorem span_M_zero (F : G.Fn) (hF : F ∈ Submodule.span G.Kf (G.M : Set G.Fn)) (i : G.comp) (L : G.P.Tup)
    (hL : ¬ G.P.IsLatTup L) : F i L = 0 := by
  have key : ∀ F' ∈ (G.M : Set G.Fn), F' i L = 0 := by
    intro F' hF'
    have h0 : F' ∈ Submodule.pi Set.univ (fun j => (G.lev j).funMod G.P.HtupW) := hF'
    have h1 := (Submodule.mem_pi.1 h0) i (Set.mem_univ i)
    have h2 := (Submodule.mem_inf.1 (Submodule.mem_inf.1 h1).1).2
    have h3 := (Submodule.mem_iInf _).1 h2 L
    have h4 := (Submodule.mem_iInf _).1 h3 hL
    exact LinearMap.mem_ker.1 h4
  induction hF using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

end Loc

section Rec

variable {D : D7} (c : LatCmp D)

def ValRat : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (x : ((D.fm u).lat 0).V)
    (i : (D.gat u w hg).comp) (L : (D.gat u w hg).P.Tup), (D.gat u w hg).P.IsLatTup L →
    ∃ Q : MvPolynomial _ D.what₂.LL, MvPolynomial.map (c.embW u w hg) Q = c.cmp u w hg x i L

theorem cmp_inj u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Function.Injective (c.cmp u w hg) := by
  refine (injective_iff_map_eq_zero (c.cmp u w hg)).2 fun x hx => ?_
  have hli := c.cmp_li u w hg
  rw [linearIndependent_iff'] at hli
  have hsum : ∑ a, (fun a => c.embW u w hg (((D.fm u).lat 0).b.repr x a)) a •
      c.cmp u w hg (((D.fm u).lat 0).b a) = 0 := by
    have h1 := congrArg (c.cmp u w hg) (((D.fm u).lat 0).b.sum_repr x)
    rw [map_sum, hx] at h1
    simpa only [c.cmp_smul] using h1
  have hz : ∀ a, ((D.fm u).lat 0).b.repr x a = 0 := fun a =>
    (c.embW u w hg).injective ((hli Finset.univ _ hsum a (Finset.mem_univ a)).trans (map_zero _).symm)
  exact ((D.fm u).lat 0).b.ext_elem fun a => by simp [hz a]

theorem cmp_mem_span u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (x : ((D.fm u).lat 0).V) :
    c.cmp u w hg x ∈ Submodule.span (D.gat u w hg).Kf ((D.gat u w hg).M : Set (D.gat u w hg).Fn) := by
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
    rw [((D.fm u).lat_good 0).2.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    apply Submodule.subset_span
    rw [← c.cmp_M u w hg]
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h1 => rw [c.cmp_smul]; exact Submodule.smul_mem _ _ h1

theorem ValRat.all (h : ValRat c) u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (x : ((D.fm u).lat 0).V) : RatFn (D.gat u w hg) (c.embW u w hg) (c.cmp u w hg x) := by
  intro i L
  by_cases hL : (D.gat u w hg).P.IsLatTup L
  · exact h u w hg x i L hL
  · refine ⟨0, ?_⟩
    rw [map_zero, span_M_zero (D.gat u w hg) _ (cmp_mem_span c u w hg x) i L hL]

theorem span_M_le u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule.span (D.gat u w hg).Kf ((D.gat u w hg).M : Set (D.gat u w hg).Fn) ≤
      Submodule.span (D.gat u w hg).Kf (Set.range (c.cmp u w hg)) := by
  rw [Submodule.span_le]
  intro F hF
  rw [← c.cmp_M u w hg] at hF
  exact Submodule.span_le_restrictScalars (D.gat u w hg).O (D.gat u w hg).Kf _
    (Submodule.span_mono (Set.image_subset_range _ _) hF)

theorem range_cmp (h : ValRat c) u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (F : (D.gat u w hg).Fn) :
    (∃ x, c.cmp u w hg x = F) ↔
      F ∈ Submodule.span (D.gat u w hg).Kf ((D.gat u w hg).M : Set (D.gat u w hg).Fn) ∧
        RatFn (D.gat u w hg) (c.embW u w hg) F := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨cmp_mem_span c u w hg x, ValRat.all c h u w hg x⟩
  · rintro ⟨hF, hr⟩
    exact rat_mem (c.embW u w hg) (evG (D.gat u w hg)) (c.cmp u w hg) (evG_sep _) (c.cmp_smul u w hg)
      (fun x => (ratFn_iff _ _ _).1 (ValRat.all c h u w hg x)) (span_M_le c u w hg hF) ((ratFn_iff _ _ _).1 hr)

theorem yv_span {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (F : G.Fn)
    (hF : F ∈ Submodule.span G.Kf (G.M : Set G.Fn)) (D' : D7) : G.yv v F ∈ Submodule.span G.Kf (G.M : Set G.Fn) := by
  induction hF using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ((Model.operators_preserve_lattices D' G).2 v y hy)
  | zero => rw [← yK_apply, map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h1 h2 => rw [← yK_apply, map_add]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h1 => rw [← yK_apply, map_smul]; exact Submodule.smul_mem _ _ h1

theorem yvRat_of_valRat (h : ValRat c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV) :
    ∃ yL : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.fm u).lat 0).V,
      ∀ x, (D.gat u w hg).yv v (c.cmp u w hg x) = c.cmp u w hg (yL x) := by
  have hex : ∀ x, ∃ y, c.cmp u w hg y = yK (D.gat u w hg) v (c.cmp u w hg x) := by
    intro x
    rw [yK_apply]
    refine (range_cmp c h u w hg _).2 ⟨yv_span (D.gat u w hg) v _ (cmp_mem_span c u w hg x) D, ?_⟩
    exact (ratFn_iff _ _ _).2 (yv_rat _ _ v _ ((ratFn_iff _ _ _).1 (ValRat.all c h u w hg x)))
  exact ⟨descOp (c.embW u w hg) (c.cmp u w hg) (c.cmp_smul u w hg) (cmp_inj c u w hg) (yK (D.gat u w hg) v) hex,
    fun x => by rw [descOp_spec, yK_apply]⟩

end Rec

end Formalism.L2.G.Cmp
