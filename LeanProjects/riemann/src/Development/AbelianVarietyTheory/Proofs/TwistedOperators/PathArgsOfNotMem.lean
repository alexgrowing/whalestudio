import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvZipFock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def sandwich {X Y Z U : Node} {A : Path T X Y} {r : Path T Y Z} {B' : Path T Z U} (α : PureT G A) (σ : TotT G r)
    (β : PureT G B') : TotT G ((A.comp r).comp B') :=
  σ.sum fun d c => Finsupp.single ((α.append d).append β) c

def RepFinAt {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {X Y : Node} (p : Path T X Y) (e : AE D) (τ : TotT G p)
    (Tl : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∃ φ : PureT G p → PureT G p, (∀ d ∈ τ.support, VecAll ρ e p (φ d) d) ∧
    ∀ x : ArgT G p, HalfAll e p x → (τ.sum fun d c => c * famProd p (φ d) x) = ∏ w ∈ locPl G t, Tl w (pathArgs B t w p x)

section Helpers

theorem arrows_comp_eq {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z), (p.comp q).arrows = p.arrows ++ q.arrows
  | _, .nil => by simp [Path.comp, Path.arrows]
  | _, .snoc a q => by simp [Path.comp, Path.arrows, arrows_comp_eq p q]

theorem onGrid_comp {m : ℕ} {t : T} {X Y Z : Node} {p : Path T X Y} {q : Path T Y Z} (hp : OnGrid m t p) (hq : OnGrid m t q) :
    OnGrid m t (p.comp q) := fun a ha => by
  rw [arrows_comp_eq] at ha
  rcases List.mem_append.1 ha with h | h
  exacts [hp a h, hq a h]

theorem onGrid_routeSmall {m : ℕ} (t : T) {i j : ℕ} (hi : i < m) (hj : j < m) : OnGrid m t (routeSmall t i j) := by
  intro a ha
  simp only [routeSmall, Path.arrows, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact Or.inr ⟨i, j, hi.le, hj, rfl⟩
  · exact Or.inl ⟨i, j, hi, hj.le, rfl⟩

theorem onGrid_routeBig {m : ℕ} (t : T) {i j : ℕ} (hi : i < m) (hj : j < m) : OnGrid m t (routeBig t i j) := by
  intro a ha
  simp only [routeBig, Path.arrows, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact Or.inl ⟨i, j + 1, hi, hj, rfl⟩
  · exact Or.inr ⟨i + 1, j, hi, hj, rfl⟩

theorem tensE_add (W : G.Weil) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ τ' : TotT G p) :
    tensE W p Q (τ + τ') = tensE W p Q τ + tensE W p Q τ' := by
  unfold tensE tensT
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun P _ => ?_
  refine Finsupp.sum_add_index' (fun _ => by simp) fun d a b => ?_
  rw [mul_add, Finsupp.single_add]

theorem tensE_zero (W : G.Weil) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) : tensE W p Q 0 = 0 := by
  unfold tensE tensT
  simp

theorem tensE_sum (W : G.Weil) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) {ι : Type} (s : Finset ι) (f : ι → TotT G p) :
    tensE W p Q (∑ κ ∈ s, f κ) = ∑ κ ∈ s, tensE W p Q (f κ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensE_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tensE_add, ih]

theorem liftT_sum (W : G.Weil) (M : Vol G) {X Y : Node} (p : Path T X Y) {ι : Type} (s : Finset ι) (f : ι → TotT G p) (F : Fn G X) :
    liftT W M p (∑ κ ∈ s, f κ) F = ∑ κ ∈ s, liftT W M p (f κ) F := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [liftT]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, liftT_add, ih]

abbrev latA (G : GridData L sc) (a : Arrow T) : AddSubgroup (WO (G.pS a.pair) (G.pT a.pair)) :=
  latO (G.pS a.pair) (G.pT a.pair) (G.latS a.pair : Set _) (G.latT a.pair : Set _) fun _ => True

theorem arrow_data {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    IsSelfDualC (G.pS a.pair) (G.latS a.pair) ∧ IsSelfDualC (G.pT a.pair) (G.latT a.pair) ∧ W.IsVac a.pair (vacOf ρ a) := by
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact ⟨isSelfDualC_neg (node_isV G hL (X := .grid (i + 1) j) ⟨hi, hj⟩).sd, (node_isV G hL (X := .grid i j) ⟨hi.le, hj⟩).sd,
      ρ.vX_is i j hi hj⟩
  · exact ⟨(node_isV G hL (X := .grid i j) ⟨hi, hj.le⟩).sd, (node_isV G hL (X := .grid i (j + 1)) ⟨hi, hj⟩).sd,
      ρ.vT_is t i j hi hj⟩

theorem exists_arrowModel {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    ∃ Tm : Sch G a →ₗ[ℂ] Sch G a,
      (∀ φ f, IsLocVec W a.pair e (vacOf ρ a) φ f ↔ IsSBHalf e (latA G a) φ ∧ f = Tm φ) ∧
      (∀ φ, IsSBHalf e (latA G a) φ → Tm φ = 0 → φ = 0) ∧
      ∀ φ, IsSBHalf e (latA G a) φ → IsThetaFunO W.ψ _ _ (Tm φ) := by
  obtain ⟨hS, hT, hv⟩ := arrow_data ρ hL ha
  obtain ⟨T₀, h0, h1⟩ := LocTensor.exists_model hS hT he hv
  obtain ⟨⟨Tm, hTm⟩, h2⟩ := h1 _ (GlobalTheory.isSBHalf_halfInd e _)
  have hm := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hi := GlobalTheory.PlaceVec.idemSum_infPart he
  have hf : vacOf ρ a ≠ 0 := by
    have h3 := hTm.vac
    rw [one_smul, ← h2 Tm hTm] at h3
    exact h3 ▸ h0
  refine ⟨Tm, fun φ f => ⟨fun h => ⟨h.1, h.2.2 Tm hTm⟩, fun h => ⟨h.1, ?_⟩⟩, fun φ hφ h => ?_, fun φ hφ => ?_⟩
  · rw [h.2, ← (h1 φ h.1).2 Tm hTm]
    exact h1 φ h.1
  · by_contra h'
    exact GlobalTheory.PlaceModelInj.placeModel_ne_zero D W.ψ _ _ _ _ e _ φ Tm W.ψ_std hS hT hm he.2 hi hTm hf hφ h' h
  · exact GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ W.ψ_std _ _ _ _ hS hT e hm hi _ hv.2.theta Tm hTm φ hφ

theorem OnGrid.init {m : ℕ} {t : T} {X : Node} {a : Arrow T} {p : Path T X a.src} (h : OnGrid m t (.snoc a p)) : OnGrid m t p :=
  fun b hb => h b (List.mem_append_left [a] hb)

theorem OnGrid.last {m : ℕ} {t : T} {X : Node} {a : Arrow T} {p : Path T X a.src} (h : OnGrid m t (.snoc a p)) :
    IsGridArrow m t a := h a (List.mem_append_right p.arrows (List.mem_singleton_self a))

theorem vecAll_unique {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ (φ φ' d : PureT G p),
      VecAll ρ e p φ d → VecAll ρ e p φ' d → φ = φ'
  | _, .nil, _, _, _, _, _, _ => rfl
  | _, .snoc a p, hg, φ, φ', d, h, h' => by
    obtain ⟨Tm, h1, h2, -⟩ := exists_arrowModel ρ hL he hg.last
    obtain ⟨a1, a2⟩ := (h1 _ _).1 h.2
    obtain ⟨b1, b2⟩ := (h1 _ _).1 h'.2
    refine Prod.ext (vecAll_unique ρ hL he p hg.init φ.1 φ'.1 d.1 h.1 h'.1) (sub_eq_zero.1 (h2 _ ?_ ?_))
    · exact (LocTensor.sbSpace e (latA G a)).sub_mem a1 b1
    · rw [map_sub, ← a2, ← b2, sub_self]

theorem vecAll_append {W : G.Weil} (ρ : RealMatch W) (e : AE D) {X Y : Node} (p : Path T X Y) (φ d : PureT G p) :
    ∀ {Z : Node} (q : Path T Y Z) (φ' d' : PureT G q),
      VecAll ρ e (p.comp q) (φ.append φ') (d.append d') ↔ VecAll ρ e p φ d ∧ VecAll ρ e q φ' d'
  | _, .nil, _, _ => (and_iff_left trivial).symm
  | _, .snoc a q, φ', d' => by
    show VecAll ρ e (p.comp q) (φ.append φ'.1) (d.append d'.1) ∧ IsLocVec W a.pair e (vacOf ρ a) φ'.2 d'.2 ↔ _
    rw [vecAll_append ρ e p φ d q φ'.1 d'.1, and_assoc]
    rfl

theorem famProd_append {X Y : Node} (p : Path T X Y) (φ : PureT G p) (x : ArgT G p) :
    ∀ {Z : Node} (q : Path T Y Z) (φ' : PureT G q) (y : ArgT G q),
      famProd (p.comp q) (φ.append φ') (x.append y) = famProd p φ x * famProd q φ' y
  | _, .nil, _, _ => (mul_one _).symm
  | _, .snoc a q, φ', y => by
    show famProd (p.comp q) (φ.append φ'.1) (x.append y.1) * φ'.2 y.2 = _ * (famProd q φ'.1 y.1 * φ'.2 y.2)
    rw [famProd_append p φ x q φ'.1 y.1, mul_assoc]

theorem halfAll_append (e : AE D) {X Y : Node} (p : Path T X Y) (x : ArgT G p) :
    ∀ {Z : Node} (q : Path T Y Z) (y : ArgT G q), HalfAll e (p.comp q) (x.append y) ↔ HalfAll e p x ∧ HalfAll e q y
  | _, .nil, _ => (and_iff_left trivial).symm
  | _, .snoc a q, y => by
    show HalfAll e (p.comp q) (x.append y.1) ∧ IsHalf e y.2 ↔ _
    rw [halfAll_append e p x q y.1, and_assoc]
    rfl

theorem exists_append {S : Arrow T → Type} {X Y : Node} (p : Path T X Y) :
    ∀ {Z : Node} (q : Path T Y Z) (z : (p.comp q).Fam S), ∃ (x : p.Fam S) (y : q.Fam S), z = x.append y
  | _, .nil, z => ⟨z, (), rfl⟩
  | _, .snoc a q, z => by
    obtain ⟨x, y, h⟩ := exists_append p q z.1
    exact ⟨x, (y, z.2), Prod.ext h rfl⟩

theorem edges_comp {X Y Z : Node} (p : Path T X Y) (q : Path T Y Z) : edges (p.comp q) = edges p ++ edges q := by
  rw [edges, arrows_comp_eq, List.map_append]; rfl

theorem edges_snoc {X : Node} (a : Arrow T) (p : Path T X a.src) : edges (.snoc a p) = edges p ++ [edgeOf a] := by
  simp [edges, Path.arrows]

theorem edges_bound {m : ℕ} {t : T} {i j : ℕ} : ∀ {Y : Node} (p : Path T (.grid i j) Y), OnGrid m t p →
    ∃ i' j', Y = .grid i' j' ∧ i ≤ i' ∧ j' ≤ j ∧ (edges p).Nodup ∧
      ∀ b ∈ edges p, i ≤ b.src.1 ∧ b.tgt.1 ≤ i' ∧ j' ≤ b.tgt.2 ∧ b.src.2 ≤ j
  | _, .nil, _ => ⟨i, j, rfl, le_rfl, le_rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | _, .snoc a p, hg => by
    obtain ⟨i', j', h1, h2, h3, h4, h5⟩ := edges_bound p hg.init
    rw [edges_snoc]
    rcases hg.last with ⟨k, l, -, -, rfl⟩ | ⟨k, l, -, -, rfl⟩
    · obtain ⟨rfl, rfl⟩ : k = i' ∧ l = j' := Node.grid.inj h1
      refine ⟨k + 1, l, rfl, by omega, h3, List.nodup_append.2 ⟨h4, List.nodup_singleton _, fun b hb c hc e => ?_⟩, fun b hb => ?_⟩
      · obtain rfl := List.mem_singleton.1 hc
        subst e
        have := (h5 _ hb).2.1
        simp [edgeOf] at this
      · rcases List.mem_append.1 hb with hb | hb
        · have := h5 b hb; omega
        · obtain rfl := List.mem_singleton.1 hb
          simp only [edgeOf]; omega
    · obtain ⟨rfl, rfl⟩ : k = i' ∧ l + 1 = j' := Node.grid.inj h1
      refine ⟨k, l, rfl, h2, by omega, List.nodup_append.2 ⟨h4, List.nodup_singleton _, fun b hb c hc e => ?_⟩, fun b hb => ?_⟩
      · obtain rfl := List.mem_singleton.1 hc
        subst e
        have := (h5 _ hb).2.2.1
        simp [edgeOf] at this
      · rcases List.mem_append.1 hb with hb | hb
        · have := h5 b hb; omega
        · obtain rfl := List.mem_singleton.1 hb
          simp only [edgeOf]; omega

theorem pathArgs_of_notMem (B : Frames G) (t : T) (w : Pl D.host.E) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y) (x : ArgT G p) (b), b ∉ edges p → pathArgs B t w p x b = 0
  | _, .nil, _, _, _ => rfl
  | _, .snoc a p, x, b, hb => by
    rw [edges_snoc, List.mem_append, not_or, List.mem_singleton] at hb
    show argAt B t w a x.2 b (pathArgs B t w p x.1 b) = 0
    rw [argAt, dif_neg (Ne.symm hb.2), pathArgs_of_notMem B t w p x.1 b hb.1]

theorem pathArgs_snoc (B : Frames G) (t : T) (w : Pl D.host.E) {X : Node} (a : Arrow T) (p : Path T X a.src)
    (x : ArgT G (.snoc a p)) :
    pathArgs B t w (.snoc a p) x = Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a x.2) := by
  funext b
  show argAt B t w a x.2 b (pathArgs B t w p x.1 b) = _
  by_cases h : edgeOf a = b
  · subst h
    rw [argAt, dif_pos rfl, Function.update_self]; rfl
  · rw [argAt, dif_neg h, Function.update_of_ne (Ne.symm h)]

theorem pathArgs_append (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : Node} (p : Path T X Y) (x : ArgT G p) :
    ∀ {Z : Node} (q : Path T Y Z) (y : ArgT G q), (∀ b ∈ edges q, b ∉ edges p) →
      pathArgs B t w (p.comp q) (x.append y) = pathArgs B t w p x + pathArgs B t w q y
  | _, .nil, _, _ => (add_zero _).symm
  | _, .snoc a q, y, h => by
    rw [edges_snoc] at h
    have h1 := pathArgs_append B t w p x q y.1 fun b hb => h b (List.mem_append_left _ hb)
    have h2 := pathArgs_of_notMem B t w p x _ (h _ (List.mem_append_right _ (List.mem_singleton_self _)))
    refine (pathArgs_snoc B t w a (p.comp q) (x.append y.1, y.2)).trans ?_
    rw [pathArgs_snoc]
    funext b
    by_cases hb : b = edgeOf a
    · subst hb
      rw [Pi.add_apply, Function.update_self, Function.update_self, h2, zero_add]
    · rw [Pi.add_apply, Function.update_of_ne hb, Function.update_of_ne hb, h1, Pi.add_apply]

end Helpers

end GlobalTheory.FlipRun

end
