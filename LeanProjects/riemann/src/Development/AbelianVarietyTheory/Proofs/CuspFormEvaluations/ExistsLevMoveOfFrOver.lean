import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SabMapEqOfLevelEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OverMove

section Bundle

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem gw_eq_of_pmaps {S S₀ : Scheme.{0}} (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e : S ⟶ X') (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) {F₁ F₂ : X' ⟶ X} (hF : F₁ = F₂)
    {w₁ : LB.Iso L' (L.pull F₁)} {w₂ : LB.Iso L' (L.pull F₂)} (g₁ : PGen w₁) (g₂ : PGen w₂) {e₀ : S₀ ⟶ X}
    {a : LB.Gen (L'.pull e)} {t : LB.Gen (L.pull e₀)} {h₁ h₂ : S ⟶ S₀} (hh : h₁ = h₂)
    (m₁ : PMaps w₁ (K := PUnit) (fun _ => e) (fun _ => e₀) (fun _ => 1) a t h₁)
    (m₂ : PMaps w₂ (K := PUnit) (fun _ => e) (fun _ => e₀) (fun _ => 1) a t h₂)
    {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) : gw w₁ f z j k = gw w₂ f z j k := by
  subst hF hh
  have : w₁ = w₂ := by
    refine gen_eq_of_eq_along_section (fun y => ?_) p e he hp ((isGen_iff _).2 g₁) ((isGen_iff _).2 g₂) ?_
    · obtain ⟨i, hi⟩ := exists_chart hL' y
      obtain ⟨j, hj⟩ := exists_chart hL (F₁ y)
      exact ⟨(fun _ => j, i), mem_pull.2 hj, hi⟩
    · rintro s ⟨J, i⟩ ⟨hj, hi⟩
      have k₁ := m₁ S (𝟙 S) s J (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)
      have k₂ := m₂ S (𝟙 S) s J (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)
      have k₃ := mul_right_cancel (k₁.symm.trans k₂)
      rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, Category.id_comp] at k₃
      exact k₃
  rw [this]

theorem gs_of_secMaps {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) {p : Y ⟶ X} {p' : Y' ⟶ X'} {pm : Y' ⟶ Y}
    (hpm : pm ≫ p = p' ≫ F)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)))
    (s' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => p') (fun _ => 1)))
    (t : LB.Sec (LB.LinComb (L.pull F) (K := Fin 1) (fun _ => p') (fun _ => 1)))
    (h₁ : SecMaps (LB.linCombIso w (K := Fin 1) (fun _ => p') (fun _ => 1)) s' t)
    (h₂ : ∀ (i : Fin 1 → L.ι)
      (h : (LB.LinComb (L.pull F) (K := Fin 1) (fun _ => p') (fun _ => 1)).U (fun _ _ => i 0) ≤
        pm ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)).U i),
      (pm.appLE _ _ h).hom (s.f i) = t.f (fun _ _ => i 0))
    {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (j : L.ι) (i : L'.ι) (hj : F (p' (r z)) ∈ L.U j) (hi : p' (r z) ∈ L'.U i) :
    gs (r ≫ pm) z _ (s.f (fun _ => j)) = (gw w (r ≫ p') z j i).val * gs r z _ (s'.f (fun _ => i)) := by
  have hle : (LB.LinComb (L.pull F) (K := Fin 1) (fun _ => p') (fun _ => 1)).U (fun _ _ => j) ≤
      pm ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)).U (fun _ => j) := fun y hy =>
    Set.mem_iInter.2 fun _ => by
      have := mem_pull.1 (Set.mem_iInter.1 hy 0)
      show (pm ≫ p) y ∈ L.U j
      rw [hpm]; exact this
  have hm : r z ∈ LB.wchart (L.pull F) (fun _ : Fin 1 => p') (fun _ _ => j) ⊓
      LB.wchart L' (fun _ : Fin 1 => p') (fun _ => i) :=
    ⟨Set.mem_iInter.2 fun _ => mem_pull.2 hj, Set.mem_iInter.2 fun _ => hi⟩
  have e₁ := gs_appLE pm _ _ hle r z hm.1 (s.f (fun _ => j))
  have e₂ := congrArg (gs r z _) (h₁ (fun _ _ => j, fun _ => i))
  rw [← e₁, h₂ (fun _ => j) hle]
  refine (gs_res r z _ hm _).symm.trans (e₂.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ((gs_unit r z _ hm _).trans (congrArg Units.val ?_)) (gs_res r z _ hm _))))
  have key : gm r z (LB.wchart (L.pull F) (fun _ : Fin 1 => p') (fun _ _ => j) ⊓
      LB.wchart L' (fun _ : Fin 1 => p') (fun _ => i))
      ((LB.linCombIso w (K := Fin 1) (fun _ => p') (fun _ => 1)).s (fun _ _ => j, fun _ => i)) =
      ∏ _k : Fin 1, gw w (r ≫ p') z j i ^ (1 : ℤ) := by
    show gm r z _ (∏ _k : Fin 1, (res _ (pullU p' _ (w.s (fun _ => j, i)))) ^ (1 : ℤ)) = _
    rw [Fin.prod_univ_one, Fin.prod_univ_one, zpow_one, zpow_one]
    exact (gm_res r z _ hm _).trans (gm_pull r p' z ((L.pull F).U (fun _ => j) ⊓ L'.U i) ⟨mem_pull.2 hj, hi⟩ _)
  rw [Fin.prod_univ_one, zpow_one] at key
  exact key

end Bundle

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₂ T : Scheme.{0}}

def RigIso {t : SAB H S} {t₂ : SAB H S₂} {r : S₂ ⟶ S} (m : SABMap t₂ t r)
    (w : LB.Iso t₂.PP.L (t.PP.L.pull m.φ)) : Prop :=
  PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec t₂.G) (fun _ => eSec t.G) (fun _ => 1) t₂.PP.rig t.PP.rig m.cm.e

theorem rigIso_of {t : SAB H S} {t₂ : SAB H S₂} {r : S₂ ⟶ S} (m : SABMap t₂ t r)
    {w : LB.Iso t₂.PP.L (t.PP.L.pull m.φ)} (h₁ : w.IsGen)
    (h₂ : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec t₂.G) (fun _ => 1)) t₂.PP.rig
      (m.cm.rigPull t.PP.L t.PP.rig)) : RigIso m w :=
  ⟨(isGen_iff w).1 h₁, (maps_iff w _ (fun _ => eSec t.G) _ t₂.PP.rig t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 h₂⟩

theorem gw_triangle {t : SAB H S} {t₂ : SAB H S₂} {u : SAB H T} {r r' : S₂ ⟶ S} {ρ : S₂ ⟶ S₂} {x : T ⟶ S₂}
    (hu : Function.Surjective u.G.hom.appTop.hom)
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t₂ t₂ ρ) (n : SABMap u t₂ x)
    (hφ : n.φ ≫ m.φ = (n.φ ≫ ν.φ) ≫ m'.φ) (hx : x ≫ r = (x ≫ ρ) ≫ r')
    {w₀ : LB.Iso t₂.PP.L (t.PP.L.pull m.φ)} {w₀' : LB.Iso t₂.PP.L (t.PP.L.pull m'.φ)}
    {w : LB.Iso t₂.PP.L (t₂.PP.L.pull ν.φ)} (h₀ : RigIso m w₀) (h₀' : RigIso m' w₀') (h : RigIso ν w)
    {Z : Scheme.{0}} (f : Z ⟶ u.G.left) (z : Z) (j : t.PP.L.ι) (i' i : t₂.PP.L.ι)
    (hj : m.φ (n.φ (f z)) ∈ t.PP.L.U j) (hi' : ν.φ (n.φ (f z)) ∈ t₂.PP.L.U i') (hi : n.φ (f z) ∈ t₂.PP.L.U i) :
    gw w₀ (f ≫ n.φ) z j i = gw w₀' ((f ≫ n.φ) ≫ ν.φ) z j i' * gw w (f ≫ n.φ) z i' i := by
  obtain ⟨v, gv, rv, -⟩ := (isPullCubical_iff n.cm t₂.cub u.cub).1 n.lin
  obtain ⟨a, Ta⟩ := exists_comp t₂.PP.isLB w₀ v h₀.1 gv t.PP.isLB u.PP.isLB
  obtain ⟨b, Tb⟩ := exists_comp t₂.PP.isLB w v h.1 gv t₂.PP.isLB u.PP.isLB
  have gb := Tb.pgen_comp t₂.PP.isLB h.1 gv
  have rb := Tb.pmaps_comp t₂.PP.isLB (fun _ => n.cm.e_comm) h.2 rv
  obtain ⟨c, Tc⟩ := exists_comp t₂.PP.isLB w₀' b h₀'.1 gb t.PP.isLB u.PP.isLB
  have ga := Ta.pgen_comp t₂.PP.isLB h₀.1 gv
  have ra := Ta.pmaps_comp t₂.PP.isLB (fun _ => n.cm.e_comm) h₀.2 rv
  have gc := Tc.pgen_comp t₂.PP.isLB h₀'.1 gb
  have rc := Tc.pmaps_comp t₂.PP.isLB (fun _ => by
    rw [← Category.assoc, n.cm.e_comm, Category.assoc, ν.cm.e_comm, Category.assoc]) h₀'.2 rb
  obtain ⟨k, hk⟩ := exists_chart u.PP.isLB (f z)
  have e := gw_eq_of_pmaps (S := T) (S₀ := S) t.PP.isLB u.PP.isLB u.G.hom (eSec u.G) (Over.w η[u.G]) hu hφ ga gc
    (h₁ := n.cm.e ≫ m.cm.e) (h₂ := (n.cm.e ≫ ν.cm.e) ≫ m'.cm.e)
    (by rw [n.base, m.base, m'.base, ν.base]; exact hx) ra rc f z j k
  have hj' : m'.φ ((n.φ ≫ ν.φ) (f z)) ∈ t.PP.L.U j := by
    have := congrArg (fun g : u.G.left ⟶ t.G.left => g (f z)) hφ
    exact (show m.φ (n.φ (f z)) = m'.φ ((n.φ ≫ ν.φ) (f z)) from this) ▸ hj
  rw [Ta Z f z j i k hj hi hk, Tc Z f z j i' k hj' hi' hk, Tb Z f z i' i k hi' hi hk, ← _root_.mul_assoc] at e
  rw [Category.assoc]
  exact mul_right_cancel e

theorem pow_left_comp {t : SAB H S} {t₂ : SAB H S₂} {f : S₂ ⟶ S} (m : SABMap t₂ t f)
    {σ : 𝟙_ (Over S₂) ⟶ t₂.G} {τ : 𝟙_ (Over S) ⟶ t.G} (h : σ.left ≫ m.φ = f ≫ τ.left) (d : ℕ) :
    (σ ^ d).left ≫ m.φ = f ≫ (τ ^ d).left := by
  obtain ⟨e, he⟩ := LevelFibre.exists_ptEquiv m.cart (𝟙 S₂) f (Category.id_comp f)
  have h₁ : e (toUnit _ ≫ σ) = toUnit _ ≫ τ := by
    apply Over.OverMorphism.ext
    rw [he, LevelFibre.unit_left, LevelFibre.unit_left, Category.id_comp]; exact h
  have h₂ := congrArg (fun w => (w ^ d).left) h₁
  simp only [← map_pow, ← MonObj.comp_pow, he, LevelFibre.unit_left, Category.id_comp] at h₂
  exact h₂

theorem sec_lift {t : SAB H S} {t₂ : SAB H S₂} {u : SAB H T} {r : S₂ ⟶ S} {x : T ⟶ S₂} {z : T ⟶ S} (hz : x ≫ r = z)
    (m : SABMap t₂ t r) (n : SABMap u t₂ x) {s : 𝟙_ (Over T) ⟶ u.G} {σ : 𝟙_ (Over S₂) ⟶ t₂.G}
    {τ : 𝟙_ (Over S) ⟶ t.G} (h₁ : σ.left ≫ m.φ = r ≫ τ.left) (h₂ : s.left ≫ n.φ ≫ m.φ = z ≫ τ.left) :
    s.left ≫ n.φ = x ≫ σ.left := by
  apply m.cart.1.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact h₂.trans (by rw [← hz, Category.assoc]; exact congrArg _ h₁.symm)
  · rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, LevelFibre.sec_w, LevelFibre.sec_w]
    exact (Category.id_comp x).trans (Category.comp_id x).symm

variable {D : Datum H} {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}

def Lev {r : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) : Prop :=
  (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left

def Fib {s : T ⟶ Sp (KA l)} (o : Obj D l (baseKA l) s) {x : T ⟶ Xo₂.X} (n : SABMap o.t Xo₂.univ.t x) : Prop :=
  (∀ a, (o.eta a).left ≫ n.φ = x ≫ (Xo₂.univ.eta a ^ (l₂.M / l.M)).left) ∧
    ∀ a, (o.etaA a).left ≫ n.φ = x ≫ (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left

theorem exists_fib {s : T ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {z : T ⟶ Xo.X} (p : ObjMap o Xo.univ z)
    {r : Xo₂.X ⟶ Xo.X} {m : SABMap Xo₂.univ.t Xo.univ.t r} (hm : Lev m) {x : T ⟶ Xo₂.X} (hz : x ≫ r = z) :
    ∃ n : SABMap o.t Xo₂.univ.t x, n.φ ≫ m.φ = p.toSABMap.φ ∧ Fib o n := by
  obtain ⟨p', hp'⟩ := LevelFibre.sab_cast hz.symm p.toSABMap
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ r x m p'
  have e : n.φ ≫ m.φ = p.toSABMap.φ := hn.symm.trans hp'
  exact ⟨n, e, fun a => sec_lift hz m n (hm.1 a) (by rw [e]; exact p.eta a),
    fun a => sec_lift hz m n (hm.2 a) (by rw [e]; exact p.etaA a)⟩

theorem exists_objMap {s : T ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {x : T ⟶ Xo₂.X}
    {n : SABMap o.t Xo₂.univ.t x} (hn : Fib o n) {r : Xo₂.X ⟶ Xo.X} {m : SABMap Xo₂.univ.t Xo.univ.t r} (hm : Lev m) :
    ∃ q : ObjMap o Xo.univ (x ≫ r), q.toSABMap.φ = n.φ ≫ m.φ := by
  obtain ⟨q, hq⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n
  have hq' : q.cm.F = n.φ ≫ m.φ := hq
  exact ⟨⟨q, fun a => by rw [hq', ← Category.assoc, hn.1, Category.assoc, hm.1, Category.assoc],
    fun a => by rw [hq', ← Category.assoc, hn.2, Category.assoc, hm.2, Category.assoc]⟩, hq⟩

theorem fib_move (hL : Laws) (hd : l.Dvd l₂) {k : Type} [Field k] {s : Sp k ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s}
    {x x' : Sp k ⟶ Xo₂.X} {n : SABMap o.t Xo₂.univ.t x} {n' : SABMap o.t Xo₂.univ.t x'} (hn : Fib o n) (hn' : Fib o n')
    {r : Xo₂.X ⟶ Xo.X} {m : SABMap Xo₂.univ.t Xo.univ.t r} (hm : Lev m) {g : Sim D} (hg : g.InGam l l₂)
    {ρ : Xo₂.X ⟶ Xo₂.X} (ν : SABMap Xo₂.univ.t Xo₂.univ.t ρ)
    (hν : ∀ a, (Xo₂.univ.eta (g.f l₂.M a)).left ≫ ν.φ = ρ ≫ (Xo₂.univ.eta a).left)
    (hx : x' = x ≫ ρ) : n'.φ = n.φ ≫ ν.φ := by
  subst hx
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν n
  obtain ⟨q, hq⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n₂
  obtain ⟨q', hq'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n'
  have hfix : ∀ a, (Xo₂.univ.eta (g.f l₂.M a) ^ (l₂.M / l.M)).left = (Xo₂.univ.eta a ^ (l₂.M / l.M)).left := fun a => by
    apply m.cart.1.hom_ext
    · refine (hm.1 _).trans (Eq.trans ?_ (hm.1 _).symm)
      rw [← sub_add_cancel (g.f l₂.M a) a, Xo.univ.eta_add,
        Xo.univ.eta_ker _ (LevelFibre.sub_mem_of_inGam hd hg a), _root_.one_mul]
    · rw [LevelFibre.sec_w, LevelFibre.sec_w]
  have e : q'.φ = q.φ := sabMap_eq_of_level_eq hL obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ _ _ _ _
    Xo.univ o _ (Or.inl inferInstance) q' q fun a => ⟨_, rfl, by
      rw [hq, hq', hn₂, ← Category.assoc, ← Category.assoc, ← Category.assoc, hn.1, hn'.1, ← hfix,
        Category.assoc x, pow_left_comp ν (hν a), hfix, Category.assoc x, Category.assoc x ρ, Category.assoc x]⟩
  apply m.cart.1.hom_ext
  · exact hq'.symm.trans (e.trans (hq.trans (by rw [hn₂])))
  · rw [← hn₂]; exact n'.cart.1.w.trans n₂.cart.1.w.symm

end Triple

end OverMove

open OverMove in

theorem exists_levMove_of_frOver : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → l.Dvd d.l₂ → d.l₂.M = l.M * d.pd → d.EtaOK → ∀ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), DeltaDat.EtaOK { d with r := r', m := m' } → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y : FrPt Xo c k) (y₂ y₂' : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → FrOver { d with r := r', m := m' } y₂' y → ∃ (g : Sim Dw) (ρ : d.Xo₂.X ≅ d.Xo₂.X) (ν : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ.hom), g.InGam l d.l₂ ∧ d.Xo₂.LevAut g ρ ∧ IsLevMove ρ.hom ν (g.f d.l₂.M) (g.f d.l₂.A) ∧ FrMove ρ.hom ν y₂ y₂' := by
  intro hL E _ _ _ H Dw l Xo c n d hN hd hM hE r' m' hE' k _ _ _ _ hk y y₂ y₂' h h'
  have hpd : d.pd = d.l₂.M / l.M := by
    rw [hM, Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) l.three_le)]
  have L₁ : Lev d.m := ⟨hpd ▸ hE.1, hE.2⟩
  have L₂ : Lev m' := ⟨hpd ▸ hE'.1, hE'.2⟩
  obtain ⟨r₀, jK, m₀, hj, hs, e₁, e₂, -, hF⟩ := hN l d.l₂ Xo d.Xo₂ hd
  have L₀ : Lev m₀ := ⟨e₁, e₂⟩
  obtain ⟨rF, f₁, f₂, -, -, -, hfib⟩ := hF c d.c₂ d.hF.symm
  obtain ⟨o, ⟨p⟩⟩ := obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y.x ≫ Xo.s) y.x rfl rfl
    (by rw [LevelFibre.spMap_id', Category.comp_id]) Xo.univ
  obtain ⟨hx, hu, w₀, pm, t, g₀, ρ₀, pa, pb, sm, ht⟩ := h
  obtain ⟨hx', hu', w₀', pm', t', g₀', ρ₀', pa', pb', sm', ht'⟩ := h'
  obtain ⟨u, hφ, F₁⟩ := exists_fib p L₁ hx
  obtain ⟨u', hφ', F₂⟩ := exists_fib p L₂ (x := y₂'.x) hx'
  have base : ∀ (z : FrPt d.Xo₂ d.c₂ k) (v : SABMap o.t d.Xo₂.univ.t z.x), Fib o v → z.x ≫ r₀ = y.x := by
    intro z v hv
    obtain ⟨q, -⟩ := exists_objMap hv L₀
    refine (Xo.rep (Sp k) (y.x ≫ Xo.s) inferInstance o).unique ⟨?_, ⟨q⟩⟩ ⟨rfl, ⟨p⟩⟩
    rw [Category.assoc, hs, ← Category.assoc, z.x_over, y.x_over, sOf, sOf, ← Geo.Tor.spMap_comp]
    congr 1
    ext a
    refine Eq.trans (congrArg (algebraMap d.c₂.F k) (Subtype.ext ?_)) (hk (IntermediateField.inclusion c.le a))
    exact hj a
  have lw : ∀ z : FrPt d.Xo₂ d.c₂ k, z.x ≫ d.Xo₂.s =
      spMap (algebraMap d.c₂.F k) ≫ spMap (IntermediateField.inclusion d.c₂.le).toRingHom := fun z =>
    z.x_over.trans (Geo.Tor.spMap_comp _ _)
  obtain ⟨⟨g, ρ, hg, hρ, -, hy⟩, -⟩ := hfib k (pullback.lift _ _ (lw y₂)) (pullback.lift _ _ (lw y₂')) (by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, f₁, pullback.lift_fst_assoc, pullback.lift_fst_assoc, base y₂ u F₁,
        base y₂' u' F₂]
    · rw [Category.assoc, Category.assoc, f₂, pullback.lift_snd_assoc, pullback.lift_snd_assoc])
  rw [pullback.lift_fst, pullback.lift_fst_assoc] at hy
  obtain ⟨hρs, ν, hν, hνA⟩ := id hρ
  have hmv : u'.φ = u.φ ≫ ν.φ := fib_move hL hd F₁ F₂ L₀ hg ν hν hy
  refine ⟨g, ρ, ν, hg, hρ, ⟨hρs, hν, hνA⟩, hy, fun τ i => ?_, ?_⟩
  · have a₁ := u.cart.1.lift_fst _ _ (y₂.tan τ i).1
    have a₂ := u.cart.1.lift_snd _ _ (y₂.tan τ i).1
    have b₁ := u'.cart.1.lift_fst _ _ (y₂'.tan τ i).1
    have b₂ := u'.cart.1.lift_snd _ _ (y₂'.tan τ i).1
    generalize u.cart.1.lift _ _ (y₂.tan τ i).1 = v at a₁ a₂
    generalize u'.cart.1.lift _ _ (y₂'.tan τ i).1 = v' at b₁ b₂
    have : v' = v := by
      apply p.cart.1.hom_ext
      · refine (congrArg (v' ≫ ·) hφ'.symm).trans (Eq.trans ?_ (congrArg (v ≫ ·) hφ))
        show v' ≫ u'.cm.F ≫ m'.φ = v ≫ u.cm.F ≫ d.m.φ
        rw [← Category.assoc, ← Category.assoc, a₁, b₁]
        exact (hu' τ i).trans (hu τ i).symm
      · exact b₂.trans a₂.symm
    rw [← a₁, ← b₁, this, Category.assoc]
    exact congrArg (v ≫ ·) hmv
  · obtain ⟨w, gw₁, rw₁, cw₁⟩ := ν.lin
    have cond : (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ y₂.x =
        (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ d.Xo₂.univ.t.G.hom := pullback.condition
    obtain ⟨q, q₁, q₂⟩ : ∃ q : Gx y₂.x ⟶ Gx y₂'.x,
        q ≫ (fst (Over.mk y₂'.x) d.Xo₂.univ.t.G).left = (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left ∧
        q ≫ (snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left = (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ ν.φ :=
      ⟨pullback.lift (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left ((snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ ν.φ) (by
        show _ ≫ y₂'.x = _
        rw [hy, ← Category.assoc, cond, Category.assoc, Category.assoc, ν.cart.1.w]),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨f, hf⟩ : ∃ f : Gx y₂.x ⟶ o.t.G.left, f ≫ u.φ = (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left :=
      ⟨_, u.cart.1.lift_fst _ _ cond.symm⟩
    have hφ₂ : u.φ ≫ d.m.φ = (u.φ ≫ ν.φ) ≫ m'.φ := by rw [← hmv, hφ, hφ']
    have hsn : (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ d.m.φ =
        ((snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ ν.φ) ≫ m'.φ := by
      rw [← hf, Category.assoc, hφ₂]; simp only [Category.assoc]
    have hq : q ≫ pm' = pm := by
      apply pullback.hom_ext
      · exact (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) pb').trans (q₁.trans pb.symm))
      · refine (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) pa').trans (Eq.trans ?_ pa.symm))
        show q ≫ _ ≫ m'.φ = _
        rw [← Category.assoc, q₂, hsn]
    refine ⟨q, w, q₁, q₂, ⟨gw₁, rw₁, cw₁⟩, fun i' i W _ h₀ h₁ h₂ => fn_ext fun z hz => ?_⟩
    have hi' : ν.φ ((snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left z) ∈ d.Xo₂.univ.t.PP.L.U i' := mem_pull.1 (h₀ hz).1
    have hi : (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left z ∈ d.Xo₂.univ.t.PP.L.U i := (h₀ hz).2
    obtain ⟨j, hj₁⟩ := exists_chart Xo.univ.t.PP.isLB (d.m.φ ((snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left z))
    have pf : u.φ (f z) = (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left z := congrArg (fun g => g z) hf
    have pq : (snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left (q z) = ν.φ ((snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left z) :=
      congrArg (fun g => g z) q₂
    have ps : d.m.φ ((snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left z) =
        m'.φ (ν.φ ((snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left z)) := congrArg (fun g => g z) hsn
    have T := gw_triangle (hL.globalFns _ _ (ObjDim.isAbelianScheme o)).2 d.m m' ν u hφ₂
      (hx.trans (hx'.symm.trans (congrArg (· ≫ r') hy))) (rigIso_of d.m g₀ ρ₀) (rigIso_of m' g₀' ρ₀')
      (rigIso_of ν gw₁ rw₁) f z j i' i (by rw [pf]; exact hj₁) (by rw [pf]; exact hi') (by rw [pf]; exact hi)
    have A := gs_of_secMaps w₀ pa y.s y₂.s t sm ht (𝟙 _) z j i hj₁ hi
    have B := gs_of_secMaps (F := m'.φ) w₀' pa' y.s y₂'.s t' sm' ht' q z j i' (by rw [pq, ← ps]; exact hj₁)
      (by rw [pq]; exact hi')
    rw [hf] at T
    rw [Category.id_comp, Category.id_comp, T] at A
    rw [hq, q₂, A, Units.val_mul, _root_.mul_assoc] at B
    have C := (Units.mul_right_inj _).1 B
    refine (gs_appLE q _ W h₁ (𝟙 _) z hz _).trans (Eq.trans ?_ (gs_mul _ z W hz _ _).symm)
    rw [Category.id_comp]
    refine C.symm.trans (congrArg₂ (· * ·) ?_ (gs_res _ z h₂ hz _).symm)
    refine Eq.trans ?_ (gs_appLE _ _ W h₀ (𝟙 _) z hz _).symm
    rw [Category.id_comp]
    exact (gs_unit (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left z _ (h₀ hz) _).symm

end GlobalTheory
