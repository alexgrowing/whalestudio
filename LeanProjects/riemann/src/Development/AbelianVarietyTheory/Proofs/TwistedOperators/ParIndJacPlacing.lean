import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.Placing

section General

variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]

def indLeft [TopologicalSpace G] [IsTopologicalGroup G] {P Q : Subgroup G}
    {σ : Representation F P V} {τ : Representation F Q V} (w : G)
    (h : ∀ q : Q, ∃ p : P, (p : G) = w * q * w⁻¹ ∧ σ p = τ q) :
    smoothPart (ind P σ) →ₗ[F] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => f.1.1 (w * g), fun q g => by
      obtain ⟨p, hp, hs⟩ := h q
      have : w * (q * g) = p * (w * g) := by rw [hp]; group
      show f.1.1 (w * (q * g)) = τ q (f.1.1 (w * g))
      rw [this, f.1.2 p, hs]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
        have hg' : ind P σ g f.1 = f.1 := hg
        apply Subtype.ext
        funext x
        have := congrFun (congrArg Subtype.val hg') (w * x)
        show f.1.1 (w * (x * g)) = f.1.1 (w * x)
        rw [← mul_assoc]
        exact this)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open ValuativeRel MeasureTheory in
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V] in

theorem _root_.GlobalTheory.SmGL.Placing.smInd_equiv [TopologicalSpace G] [IsTopologicalGroup G]
    {P Q : Subgroup G}
    {σ : Representation F P V} {τ : Representation F Q V} (w : G)
    (h : ∀ q : Q, ∃ p : P, (p : G) = w * q * w⁻¹ ∧ σ p = τ q)
    (h' : ∀ p : P, ∃ q : Q, (q : G) = w⁻¹ * p * w⁻¹⁻¹ ∧ τ q = σ p) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd P σ).Equiv (_root_.GlobalTheory.PRep.smInd Q τ)) := by
  refine ⟨Representation.Equiv.mk
    { _root_.GlobalTheory.SmGL.Placing.indLeft w h with
      invFun := _root_.GlobalTheory.SmGL.Placing.indLeft w⁻¹ h'
      left_inv := fun f => ?_
      right_inv := fun f => ?_ } fun g => ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (mul_inv_cancel_left w x)
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (inv_mul_cancel_left w x)
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (mul_assoc w x g)

open ValuativeRel MeasureTheory in
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V] in

lemma _root_.GlobalTheory.SmGL.Placing.twKer_le (π : Representation F G V)
    {N N' : Subgroup G} (w : G) (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') :
    _root_.GlobalTheory.PRep.twKer π N 1 ≤ (_root_.GlobalTheory.PRep.twKer π N' 1).comap (π w) := by
  unfold _root_.GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro _ ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨⟨w * u * w⁻¹, h u u.2⟩, π w v, ?_⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, map_mul, Module.End.mul_apply]
  rw [← Module.End.mul_apply (π w⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

open ValuativeRel MeasureTheory in
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V] in

theorem _root_.GlobalTheory.SmGL.Placing.jacquet_equiv (π : Representation F G V) {N N' : Subgroup G}
    {s s' : M →* G}
    (hs : ∀ g, s g ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ g, s' g ∈ Subgroup.normalizer (N' : Set G)) (χ : M →* Fˣ) (w : G)
    (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') (h' : ∀ u ∈ N', w⁻¹ * u * w⁻¹⁻¹ ∈ N)
    (hw : ∀ g, w * s g * w⁻¹ = s' g) :
    Nonempty ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).Equiv
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ)) := by
  have hK := _root_.GlobalTheory.SmGL.Placing.twKer_le π w h
  have hK' := _root_.GlobalTheory.SmGL.Placing.twKer_le π w⁻¹ h'
  have hinv : ∀ a b : G, a * b = 1 → ∀ v, π a (π b v) = v := fun a b hab v => by
    rw [← Module.End.mul_apply, ← map_mul, hab, map_one, Module.End.one_apply]
  let eq : _root_.GlobalTheory.PRep.Jacquet π N ≃ₗ[F] _root_.GlobalTheory.PRep.Jacquet π N' :=
    LinearEquiv.ofLinear ((_root_.GlobalTheory.PRep.twKer π N 1).mapQ _ (π w) hK)
      ((_root_.GlobalTheory.PRep.twKer π N' 1).mapQ _ (π w⁻¹) hK')
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp [hinv w w⁻¹ (mul_inv_cancel w)]))
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp [hinv w⁻¹ w (inv_mul_cancel w)]))
  refine ⟨Representation.Equiv.mk eq fun g => ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (_root_.GlobalTheory.PRep.twKer π N 1) x
  have hv : π w (π (s g) v) = π (s' g) (π w v) := by
    rw [← hw g, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hinv w⁻¹ w (inv_mul_cancel w)]
  simp [eq, _root_.GlobalTheory.SmGL.twist, _root_.GlobalTheory.PRep.jacquet, hv]

end General

section Blocks

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def Moves {ι : Type} (e e' : ι ≃ n) (w : GL n R) : Prop :=
  ∀ (g : GL n R) x y, ((w * g * w⁻¹ : GL n R) : Matrix n n R) (e' x) (e' y) =
    (g : Matrix n n R) (e x) (e y)

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.SmGL.Placing.exists_moves {ι : Type} (e e' : ι ≃ n) :
    ∃ w : GL n R, _root_.GlobalTheory.SmGL.Placing.Moves e e' w := by
  let σ : n ≃ n := e.symm.trans e'
  refine ⟨⟨σ.symm.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, ?_, ?_⟩, fun g x y => ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · simp [σ, Units.inv_mk, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

theorem Moves.symm {ι : Type} {e e' : ι ≃ n} {w : GL n R} (h : Moves e e' w) : Moves e' e w⁻¹ := by
  intro g x y
  rw [← h]
  congr 2
  group

variable {e e' : (Σ a, m a) ≃ n} {w : GL n R}

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem Moves.parab (h : Moves e e' w) {g : GL n R} (hg : g ∈ parab R e) :
    w * g * w⁻¹ ∈ parab R e' :=
  mem_parab_iff.2 fun a b i j hab => (h g _ _).trans (mem_parab_iff.1 hg a b i j hab)

theorem Moves.unipRad (h : Moves e e' w) {g : GL n R} (hg : g ∈ unipRad R e) :
    w * g * w⁻¹ ∈ unipRad R e' :=
  mem_unipRad.2 ⟨h.parab (mem_unipRad.1 hg).1,
    fun a i j => (h g _ _).trans ((mem_unipRad.1 hg).2 a i j)⟩

theorem Moves.leviProj (h : Moves e e' w) (p : SmGL.parab R e) :
    leviProj R e' ⟨_, h.parab p.2⟩ = leviProj R e p := by
  funext a
  ext i j
  exact h p _ _

omit [LinearOrder α] in

theorem Moves.leviEmb (h : Moves e e' w) (g : Levi R m) :
    w * leviEmb R e g * w⁻¹ = leviEmb R e' g := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e'.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e'.surjective j
  rw [h]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same]
  · rw [leviEmb_apply_ne R e g hab, leviEmb_apply_ne R e' g hab]

end Blocks

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
private theorem moves_inv_of_moves {ι : Type} {e e' : ι ≃ n} {w : GL n R}
    (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w) : _root_.GlobalTheory.SmGL.Placing.Moves e' e w⁻¹ := by
  intro g x y
  have := hw (w⁻¹ * g * w⁻¹⁻¹) x y
  rw [← this]
  congr 2
  group

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem conj_mem_parab_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    {g : GL n R} (hg : g ∈ _root_.GlobalTheory.SmGL.parab R e) :
    w * g * w⁻¹ ∈ _root_.GlobalTheory.SmGL.parab R e' := by
  have hg' : Matrix.BlockTriangular (g : Matrix n n R) (_root_.GlobalTheory.SmGL.blk e) := hg
  change Matrix.BlockTriangular _ (_root_.GlobalTheory.SmGL.blk e')
  intro i j hij
  obtain ⟨x, rfl⟩ := e'.surjective i
  obtain ⟨y, rfl⟩ := e'.surjective j
  rw [hw]
  exact hg' (by simpa [_root_.GlobalTheory.SmGL.blk] using hij)

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem leviProj_conj_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    _root_.GlobalTheory.SmGL.leviProj R e' ⟨w * p * w⁻¹, conj_mem_parab_of_moves hw p.2⟩ =
      _root_.GlobalTheory.SmGL.leviProj R e p := by
  refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
  simpa [_root_.GlobalTheory.SmGL.leviProj, _root_.GlobalTheory.SmGL.diagBlock] using hw (p : GL n R) ⟨a, i⟩ ⟨a, j⟩

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem conj_mem_unipRad_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    {u : GL n R} (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) :
    w * u * w⁻¹ ∈ _root_.GlobalTheory.SmGL.unipRad R e' := by
  have hP := _root_.GlobalTheory.SmGL.unipRad_le_parab R e hu
  have h1 := (_root_.GlobalTheory.SmGL.coe_mem_unipRad R (p := ⟨u, hP⟩)).1 hu
  exact (_root_.GlobalTheory.SmGL.coe_mem_unipRad R
    (p := ⟨w * u * w⁻¹, conj_mem_parab_of_moves hw hP⟩)).2
    ((leviProj_conj_of_moves hw ⟨u, hP⟩).trans h1)

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem leviEmb_conj_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    (x : _root_.GlobalTheory.SmGL.Levi R m) :
    w * _root_.GlobalTheory.SmGL.leviEmb R e x * w⁻¹ = _root_.GlobalTheory.SmGL.leviEmb R e' x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨p, rfl⟩ := e'.surjective i
  obtain ⟨q, rfl⟩ := e'.surjective j
  rw [hw]
  simp [_root_.GlobalTheory.SmGL.leviEmb, Matrix.reindex_apply]

open ValuativeRel MeasureTheory in

theorem _root_.GlobalTheory.SmGL.Placing.parInd_jac_placing : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α]
    [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e e' : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V],
    (∀ ρ : Representation ℂ (_root_.GlobalTheory.SmGL.Levi k m) V,
      Nonempty ((_root_.GlobalTheory.SmGL.parInd e ρ).Equiv (_root_.GlobalTheory.SmGL.parInd e' ρ))) ∧
    ∀ π : Representation ℂ (GL n k) V,
      Nonempty ((_root_.GlobalTheory.SmGL.jac e π).Equiv (_root_.GlobalTheory.SmGL.jac e' π)) := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e e' V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · obtain ⟨w, hw⟩ := _root_.GlobalTheory.SmGL.Placing.exists_moves (R := k) e' e
    have hw' := moves_inv_of_moves hw
    exact _root_.GlobalTheory.SmGL.Placing.smInd_equiv w
      (fun q => ⟨⟨_, conj_mem_parab_of_moves hw q.2⟩, rfl, by
        simp only [MonoidHom.comp_apply]
        rw [leviProj_conj_of_moves hw q]⟩)
      (fun p => ⟨⟨_, conj_mem_parab_of_moves hw' p.2⟩, rfl, by
        simp only [MonoidHom.comp_apply]
        rw [leviProj_conj_of_moves hw' p]⟩)
  · obtain ⟨w, hw⟩ := _root_.GlobalTheory.SmGL.Placing.exists_moves (R := k) e e'
    have hw' := moves_inv_of_moves hw
    exact _root_.GlobalTheory.SmGL.Placing.jacquet_equiv π _ _ _ w
      (fun u hu => conj_mem_unipRad_of_moves hw hu)
      (fun u hu => conj_mem_unipRad_of_moves hw' hu)
      (leviEmb_conj_of_moves hw)

end GlobalTheory.SmGL.Placing
