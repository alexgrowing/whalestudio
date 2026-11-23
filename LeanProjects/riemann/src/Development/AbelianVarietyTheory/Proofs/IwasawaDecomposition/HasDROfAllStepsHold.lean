import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFramesStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LocM.MapComp GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc

namespace GlobalTheory.LocM.StepFrame

section Lin

theorem uniq_iff {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {n : ℕ} (v : Fin n → N) :
    (∀ z : N, ∃! a : Fin n → R, z = ∑ i, a i • v i) ↔ LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination, ← Fintype.range_linearCombination,
    LinearMap.range_eq_top]
  refine Iff.trans ?_ (Function.bijective_iff_existsUnique (Fintype.linearCombination R v)).symm
  simp only [Fintype.linearCombination_apply, eq_comm]

theorem basis_iff_det {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {n : ℕ} {b V : Fin n → N}
    (hb : LinearIndependent R b ∧ Submodule.span R (Set.range b) = ⊤) (A : Fin n → Fin n → R)
    (hA : ∀ i, V i = ∑ j, A i j • b j) :
    (LinearIndependent R V ∧ Submodule.span R (Set.range V) = ⊤) ↔ IsUnit (Matrix.of A).det := by
  let B : Module.Basis (Fin n) R N := Module.Basis.mk hb.1 hb.2.ge
  rw [B.is_basis_iff_det, Module.Basis.det_apply, ← Matrix.det_transpose]
  have : (B.toMatrix V).transpose = Matrix.of A := by
    ext i j
    have e : V i = ∑ j, A i j • B j := by simpa [B] using hA i
    rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, e]
    exact congrFun (B.repr_sum_self (A i)) j
  rw [this]

variable {k N : Type} [Field k] [AddCommGroup N] [Module k N]

theorem exists_choice : ∀ (m : ℕ) (c : ∀ i : Fin m, Fin (i + 1) → N), (∀ i, LinearIndependent k (c i)) →
    ∃ s : ∀ i : Fin m, Fin (i + 1), LinearIndependent k fun i => c i (s i)
  | 0, c, _ => ⟨fun i => i.elim0, linearIndependent_empty_type⟩
  | m + 1, c, hc => by
    obtain ⟨s, hs⟩ := exists_choice m (fun i => c i.castSucc) fun i => hc _
    obtain ⟨j, hj⟩ : ∃ j, c (Fin.last m) j ∉ Submodule.span k (Set.range fun i : Fin m => c i.castSucc (s i)) := by
      by_contra! h
      have : FiniteDimensional k (Submodule.span k (Set.range fun i : Fin m => c i.castSucc (s i))) :=
        FiniteDimensional.span_of_finite k (Set.finite_range _)
      have h1 := Submodule.finrank_mono (Submodule.span_le.2 (Set.range_subset_iff.2 h))
      rw [finrank_span_eq_card hs, finrank_span_eq_card (hc _)] at h1
      simp at h1
    refine ⟨Fin.lastCases j s, ?_⟩
    rw [linearIndependent_finSucc']
    have e : Fin.init (fun i : Fin (m + 1) => c i (Fin.lastCases (motive := fun i : Fin (m + 1) => Fin (i + 1)) j s i)) =
        fun i : Fin m => c i.castSucc (s i) := funext fun i => by simp [Fin.init]
    rw [e]
    exact ⟨hs, by simpa using hj⟩

theorem head_le_head {μ n r : ℕ} {u : Fin μ → N} {v : Fin n → N} (hu : LinearIndependent k u) (hr : r ≤ μ)
    (h : (head r u : Submodule k N) ≤ head r v) : r ≤ n ∧ (head r v : Submodule k N) ≤ head r u := by
  have hl' : LinearIndependent k fun j : {j : Fin μ // (j : ℕ) < r} => u j := hu.comp _ Subtype.val_injective
  have : FiniteDimensional k (head r v : Submodule k N) := FiniteDimensional.span_of_finite k (Set.finite_range _)
  have h1 : Module.finrank k (head r u : Submodule k N) = r := by
    rw [head, finrank_span_eq_card hl', Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hr]
  have h2 : Module.finrank k (head r v : Submodule k N) ≤ min n r := by
    refine (finrank_range_le_card (R := k) _).trans ?_
    rw [Fintype.card_subtype, Fin.card_filter_val_lt]
  have h3 := Submodule.finrank_mono h
  exact ⟨by omega, (Submodule.eq_of_le_of_finrank_le h (by omega)).ge⟩

theorem IsBas.indep {m : ℕ} {M : Submodule k N} {b : Fin m → N} (hb : IsBas M b) : LinearIndependent k b :=
  linearIndependent_iff_injective_fintypeLinearCombination.2 ((isBas_iff M b).1 hb).1

theorem isBas_of_indep {m : ℕ} {M : Submodule k N} {b c : Fin m → N} (hb : IsBas M b) (hc : LinearIndependent k c)
    (hm : ∀ i, c i ∈ M) : IsBas M c := by
  have e := ((isBas_iff M b).1 hb).2
  rw [Fintype.range_linearCombination] at e
  have : FiniteDimensional k M := e ▸ FiniteDimensional.span_of_finite k (Set.finite_range _)
  rw [isBas_iff, Fintype.range_linearCombination]
  refine ⟨linearIndependent_iff_injective_fintypeLinearCombination.1 hc,
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (Set.range_subset_iff.2 hm)) ?_⟩
  rw [finrank_span_eq_card hc, ← e, finrank_span_eq_card (IsBas.indep hb)]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Tan

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S]

def Bas (t : SAB H X) (x : Sp R ⟶ X) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (v i)) ∧ ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u

theorem bas_iff_full {x : Sp R ⟶ X} {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ i, IsTanAtG t x (v i)) : Bas t x v ↔ FrameBC.Full fun i => LieMet.tanOf (hv i) :=
  ⟨fun h z => (existsUnique_congr fun a => LieMet.isComb_iff (fun i => LieMet.tanOf (hv i)) a z).1
      (h.2 _ (LieMet.isTan_tv z)),
    fun h => ⟨hv, fun u hu => (existsUnique_congr fun a =>
      LieMet.isComb_iff (fun i => LieMet.tanOf (hv i)) a (LieMet.tanOf hu)).2 (h _)⟩⟩

theorem Bas.bc {x : Sp R ⟶ X} {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h : Bas t x v) (ψ : R →+* S) :
    Bas t (spMap ψ ≫ x) fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ v i := by
  have h1 := FrameBC.full_bc ψ ((bas_iff_full h.1).1 h)
  exact (bas_iff_full (v := fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ v i)
    fun i => LieMet.isTan_map ψ rfl (h.1 i)).2 h1

theorem Bas.congr {x x' : Sp R ⟶ X} {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h : Bas t x v)
    (e : x = x') : Bas t x' v := e ▸ h

theorem bc_bc {T : Type} [CommRing T] (φ : R →+* S) (ψ : S →+* T) (v : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (Formalism.L2.Pj.dualMap φ) ≫ v = spMap (Formalism.L2.Pj.dualMap (ψ.comp φ)) ≫ v := by
  have e : (Formalism.L2.Pj.dualMap ψ).comp (Formalism.L2.Pj.dualMap φ) = Formalism.L2.Pj.dualMap (ψ.comp φ) :=
    RingHom.ext fun z => by ext <;> simp [Formalism.L2.Pj.dualMap]
  rw [← Category.assoc, sp_comp, e]

theorem bas_iff_det {x : Sp R ⟶ X} {n : ℕ} {b V : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hb : Bas t x b)
    (hV : ∀ i, IsTanAtG t x (V i)) (A : Fin n → Fin n → R) (hA : ∀ i, IsCombAtG t x b (A i) (V i)) :
    Bas t x V ↔ IsUnit (Matrix.of A).det := by
  have h1 := (uniq_iff (R := R) fun i => LieMet.tanOf (hb.1 i)).1 ((bas_iff_full hb.1).1 hb)
  have h2 := basis_iff_det (V := fun i => LieMet.tanOf (hV i)) h1 A fun i =>
    (LieMet.isComb_iff (fun i => LieMet.tanOf (hb.1 i)) (A i) (LieMet.tanOf (hV i))).1 (hA i)
  exact (bas_iff_full hV).trans ((uniq_iff (R := R) fun i => LieMet.tanOf (hV i)).trans h2)

theorem exists_select {x : Sp R ⟶ X} {g : ℕ} (n : Fin (g + 1) → ℕ)
    (v : ∀ r, Fin (n r) → (Sp (DualNumber R) ⟶ t.G.left)) (hv : ∀ r, Bas t x (v r)) (hn : ∀ r : Fin (g + 1), (r : ℕ) ≤ n r)
    {K : Type} [Field K] (φ : R →+* K) :
    ∃ (f : R) (m : ℕ) (V : Fin m → (Sp (DualNumber R) ⟶ t.G.left)) (e : Fin g ↪ Fin m), φ f ≠ 0 ∧
      (∀ i : Fin g, ∃ j : Fin (n i.succ), (j : ℕ) < i + 1 ∧ V (e i) = v i.succ j) ∧
      ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ f) →
        Bas t (spMap ψ ≫ x) fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ V i := by
  let κ : Fin (n (Fin.last g)) → Fin (g + 1) := fun i => ⟨min (i + 1) g, by omega⟩
  have hκ : ∀ i : Fin (n (Fin.last g)), (i : ℕ) + 1 ≤ n (κ i) := fun i => by
    by_cases h : (i : ℕ) + 1 ≤ g
    · exact (min_eq_left h).ge.trans (hn (κ i))
    · have : κ i = Fin.last g := Fin.ext (min_eq_right (by omega))
      rw [this]
      exact i.2
  have hb := fun r => (uniq_iff (R := K) fun i => LieMet.tanOf (((hv r).bc φ).1 i)).1
    ((bas_iff_full ((hv r).bc φ).1).1 ((hv r).bc φ))
  obtain ⟨s, hs⟩ := exists_choice (k := K) _
    (fun i j => LieMet.tanOf (((hv (κ i)).bc φ).1 (Fin.castLE (hκ i) j)))
    fun i => (hb (κ i)).1.comp _ (Fin.castLE_injective (hκ i))
  let V : Fin (n (Fin.last g)) → (Sp (DualNumber R) ⟶ t.G.left) := fun i => v (κ i) (Fin.castLE (hκ i) (s i))
  have hV : ∀ i, IsTanAtG t x (V i) := fun i => (hv _).1 _
  choose A hA using fun i => ((hv (Fin.last g)).2 _ (hV i)).exists
  have key : ∀ (S : Type) [CommRing S] (ψ : R →+* S),
      (Bas t (spMap ψ ≫ x) fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ V i) ↔ IsUnit (ψ (Matrix.of A).det) := by
    intro S _ ψ
    rw [bas_iff_det ((hv _).bc ψ) (fun i => LieMet.isTan_map ψ rfl (hV i)) _ fun i => comb_bc ψ (hA i),
      RingHom.map_det]
    rfl
  refine ⟨(Matrix.of A).det, _, V, Fin.castLEEmb (hn (Fin.last g)), IsUnit.ne_zero ((key K φ).1 ?_), fun i => ?_,
    fun S _ ψ h => (key S ψ).2 h⟩
  · refine (bas_iff_full (v := fun i => spMap (Formalism.L2.Pj.dualMap φ) ≫ V i) fun i => LieMet.isTan_map φ rfl (hV i)).2
      ((uniq_iff (R := K) fun i => LieMet.tanOf (LieMet.isTan_map φ rfl (hV i))).2 ⟨hs, ?_⟩)
    let B := Module.Basis.mk (hb (Fin.last g)).1 (hb (Fin.last g)).2.ge
    have := Module.Finite.of_basis B
    exact hs.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis B).symm
  · have e : κ (Fin.castLEEmb (hn (Fin.last g)) i) = i.succ := Fin.ext (min_eq_left (show (i : ℕ) + 1 ≤ g from i.2))
    have : ∀ r (_ : r = i.succ) (j : Fin (n r)), (j : ℕ) < i + 1 → ∃ j' : Fin (n i.succ), (j' : ℕ) < i + 1 ∧
        v r j = v i.succ j' := by
      rintro _ rfl j hj
      exact ⟨j, hj, rfl⟩
    exact this _ e _ (s _).2

variable {k : Type} [Field k] {x : Sp k ⟶ X} {l : Level H} {c : Coeff l} {f : c.F →+* k} {u : Vecs Dw t k}

theorem step_eq (hu : IsFrame t f x u) {σ : E →+* ℂ} {r n : ℕ} (hr : r ≤ Dw.mult σ)
    {v : Fin n → (Sp (DualNumber k) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j))
    (h : ∀ i : Fin (Dw.mult σ), (i : ℕ) < r → ∃ cf : Fin n → k, (∀ j : Fin n, r ≤ (j : ℕ) → cf j = 0) ∧
      IsCombAtG t x v cf (u σ i)) :
    r ≤ n ∧ ∀ j : Fin n, (j : ℕ) < r → ∃ cf : Fin (Dw.mult σ) → k,
      (∀ i : Fin (Dw.mult σ), r ≤ (i : ℕ) → cf i = 0) ∧ IsCombAtG t x (u σ) cf (v j) := by
  obtain ⟨N, xc, hx⟩ := EigLoc.exists_chart t x
  obtain ⟨b, rfl⟩ := exists_coord hx u fun σ i => (hu.1 σ i).1
  choose d hd using fun j => vec_exists hx (v j) (hv j)
  obtain rfl : v = fun j => vec t x xc (d j) := funext hd
  rw [isFrame_iff hx] at hu
  simp only [comb_iff hx, ← mem_head] at h ⊢
  have := head_le_head (v := d) (IsBas.indep (hu σ)) hr
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun i => h i i.2))
  exact ⟨this.1, fun j hj => this.2 (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)⟩

theorem isFrame_of_steps (hu : IsFrame t f x u) {w : Vecs Dw t k} (ty : (E →+* ℂ) → Finset ℕ)
    (hw : ∀ σ (i : Fin (Dw.mult σ)), ∃ cf : Fin (Dw.mult σ) → k,
      (∀ j : Fin (Dw.mult σ), (i : ℕ) + 1 ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG t x (u σ) cf (w σ i))
    (hb : ∀ σ, ∃ (n : ℕ) (v : Fin n → (Sp (DualNumber k) ⟶ t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n),
      (∀ i, v (e i) = w σ i) ∧ Bas t x v) : IsFrame t f x w ∧ SameFlag ty t x u w := by
  refine ⟨?_, fun σ r _ i hi => (hw σ i).imp fun cf h => ⟨fun j hj => h.1 j (by omega), h.2⟩⟩
  obtain ⟨N, xc, hx⟩ := EigLoc.exists_chart t x
  obtain ⟨b, rfl⟩ := exists_coord hx u fun σ i => (hu.1 σ i).1
  choose n v e he hv using hb
  choose d hd using fun σ j => vec_exists hx (v σ j) ((hv σ).1 j)
  obtain rfl : v = fun σ j => vec t x xc (d σ j) := funext fun σ => funext (hd σ)
  obtain rfl : w = fun σ i => vec t x xc (d σ (e σ i)) := funext fun σ => funext fun i => (he σ i).symm
  rw [isFrame_iff hx] at hu ⊢
  intro σ
  refine isBas_of_indep (hu σ) (LinearIndependent.comp ((uniq_iff (d σ)).1 fun z => ?_).1 _ (e σ).injective) fun i => ?_
  · simpa only [comb_iff hx] using (hv σ).2 _ (vec_tan hx z)
  · obtain ⟨cf, -, h⟩ := hw σ i
    rw [(comb_iff hx _ _ _).1 h]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ((hu σ).1 j)

end Tan

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

abbrev resR {X : Scheme.{0}} {U U' : X.Opens} (h : U' ≤ U) : Γ(X, U) →+* Γ(X, U') :=
  (X.presheaf.map (homOfLE h).op).hom

theorem spMap_resR {X : Scheme.{0}} {U U' : X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U) :
    spMap (resR h) ≫ hU.fromSpec = hU'.fromSpec := hU.map_fromSpec hU' (homOfLE h).op

def Adapted (Z : Mdl Y i₀) (σ : E →+* ℂ) (r : ℕ) {U : Z.X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) : Prop :=
  Bas (Y Z.i).t (hU.fromSpec ≫ Z.π) v ∧ ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k) (u : Vecs Dw (Y Z.i).t k),
    Z.FlagAt (spMap φ ≫ hU.fromSpec) u → ∀ i : Fin (Dw.mult σ), (i : ℕ) < r → ∃ cf : Fin n → k,
      (∀ j : Fin n, r ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z.π)
        (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ v j) cf (u σ i)

theorem Adapted.res {Z : Mdl Y i₀} {σ : E →+* ℂ} {r : ℕ} {U U' : Z.X.Opens} {hU : IsAffineOpen U} {n : ℕ}
    {v : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)} (h : Adapted Z σ r hU v) (hU' : IsAffineOpen U')
    (hle : U' ≤ U) : Adapted Z σ r hU' fun j => spMap (Formalism.L2.Pj.dualMap (resR hle)) ≫ v j := by
  have e := spMap_resR hU hU' hle
  refine ⟨?_, fun k _ φ u => ?_⟩
  · exact (Bas.bc (R := Γ(Z.X, U)) h.1 (resR hle)).congr
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Z.π) e))
  · have := h.2 k (φ.comp (resR hle)) u
    have e' : spMap (φ.comp (resR hle)) ≫ hU.fromSpec = spMap φ ≫ hU'.fromSpec := by
      rw [← sp_comp, Category.assoc, e]
    rw [e'] at this
    simpa only [bc_bc] using this

theorem Adapted.step {Z : Mdl Y i₀} {σ : E →+* ℂ} {r : ℕ} {U : Z.X.Opens} {hU : IsAffineOpen U} {n : ℕ}
    {v : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)} (h : Adapted Z σ r hU v) (hr : r ≤ Dw.mult σ)
    {k : Type} [Field k] (φ : Γ(Z.X, U) →+* k) {u : Vecs Dw (Y Z.i).t k} (hu : Z.FlagAt (spMap φ ≫ hU.fromSpec) u) :
    r ≤ n ∧ ∀ j : Fin n, (j : ℕ) < r → ∃ cf : Fin (Dw.mult σ) → k, (∀ i : Fin (Dw.mult σ), r ≤ (i : ℕ) → cf i = 0) ∧
      IsCombAtG (Y Z.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (u σ) cf (spMap (Formalism.L2.Pj.dualMap φ) ≫ v j) := by
  have h2 := h.2 k φ u hu
  obtain ⟨a, ψ, -, fu, -⟩ := hu
  exact step_eq fu hr (fun j => LieMet.isTan_map φ (Category.assoc _ _ _).symm (h.1.1 j)) h2

theorem exists_flagAt (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) {x : Z.X} (hx : x ∈ U) :
    ∃ (k : Type) (_ : Field k) (φ : Γ(Z.X, U) →+* k) (u : Vecs Dw (Y Z.i).t k), Z.FlagAt (spMap φ ≫ hU.fromSpec) u := by
  obtain ⟨y, hyU, hy⟩ := Z.dense.inter_open_nonempty U U.2 ⟨x, hx⟩
  have hr : Set.range (Z.X.fromSpecResidueField y) = {y} := Scheme.range_fromSpecResidueField y
  have := hU.isOpenImmersion_fromSpec
  have h' : Set.range (Z.X.fromSpecResidueField y) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec, hr]
    exact Set.singleton_subset_iff.2 hyU
  obtain ⟨a, ψ, ha⟩ := Z.exists_chart (k := Z.X.residueField y) (Z.X.fromSpecResidueField y)
    (hr.le.trans (Set.singleton_subset_iff.2 hy))
  refine ⟨Z.X.residueField y, inferInstance,
    (Spec.preimage (IsOpenImmersion.lift hU.fromSpec (Z.X.fromSpecResidueField y) h')).hom, _,
    CommonMod.flagAt_chart Z (ha.trans ?_)⟩
  show _ = Spec.map (Spec.preimage _) ≫ _
  rw [Spec.map_preimage]
  exact (IsOpenImmersion.lift_fac _ _ _).symm

theorem exists_intFrame (Z : Mdl Y i₀) (x : Z.X)
    (h : ∀ σ (r : Fin (Dw.mult σ + 1)), ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (n : ℕ)
      (v : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)), x ∈ U ∧ Adapted Z σ r hU v) :
    ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), x ∈ U ∧ IntFrame Z hU w := by
  classical
  choose U₀ hU₀ n v₀ hx₀ hv₀ using h
  have ho : IsOpen (⋂ q : Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1), (U₀ q.1 q.2 : Set Z.X)) :=
    isOpen_iInter_of_finite fun q => (U₀ q.1 q.2).2
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, hle⟩ := Z.X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_iInter.2 fun q : Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1) => hx₀ q.1 q.2) ho
  have hU : IsAffineOpen U := hU
  have hle' : ∀ σ r, U ≤ U₀ σ r := fun σ r => fun y hy => Set.mem_iInter.1 (hle hy) ⟨σ, r⟩
  obtain ⟨v, hv⟩ : ∃ v : ∀ σ r, Fin (n σ r) → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left),
      ∀ σ (r : Fin (Dw.mult σ + 1)), Adapted Z σ r hU (v σ r) := ⟨_, fun σ r => (hv₀ σ r).res hU (hle' σ r)⟩
  obtain ⟨k₀, _, φ₀, u₀, hu₀⟩ := exists_flagAt Z hU hx
  choose f m V e hf hV hB using fun σ => exists_select (n σ) (v σ) (fun r => (hv σ r).1)
    (fun r => ((hv σ r).step (Nat.lt_succ_iff.1 r.2) φ₀ hu₀).1) (K := Z.X.residueField x) (Z.X.evaluation U x hx).hom
  have hU' := hU.basicOpen (∏ σ, f σ)
  have hle₂ := Z.X.basicOpen_le (∏ σ, f σ)
  have e₂ := spMap_resR hU hU' hle₂
  have hu : ∀ σ, IsUnit (resR hle₂ (f σ)) := fun σ =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem f (Finset.mem_univ σ)))
      (Z.X.toRingedSpace.isUnit_res_basicOpen (∏ σ, f σ))
  have hB' : ∀ σ, Bas (Y Z.i).t (hU'.fromSpec ≫ Z.π) fun i => spMap (Formalism.L2.Pj.dualMap (resR hle₂)) ≫ V σ i :=
    fun σ => (hB σ _ _ (hu σ)).congr ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Z.π) e₂))
  refine ⟨_, hU', fun σ i => spMap (Formalism.L2.Pj.dualMap (resR hle₂)) ≫ V σ (e σ i), ?_,
    fun σ => ⟨m σ, _, e σ, fun _ => rfl, hB' σ⟩, fun k _ φ hφ => ?_⟩
  · rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen _ x hx, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun σ _ => hf σ
  · obtain ⟨a, ψ, ha⟩ := Z.exists_chart _ hφ
    have fu := CommonMod.flagAt_chart Z ha
    have e₃ : spMap (φ.comp (resR hle₂)) ≫ hU.fromSpec = spMap φ ≫ hU'.fromSpec := by
      rw [← sp_comp, Category.assoc, e₂]
    have fu' := fu
    rw [← e₃] at fu'
    obtain ⟨b, χ, hb, fr, sf⟩ := fu
    have key := isFrame_of_steps fr Z.ty
      (w := Vecs.bc φ fun σ i => spMap (Formalism.L2.Pj.dualMap (resR hle₂)) ≫ V σ (e σ i)) (fun σ i => ?_) fun σ => ?_
    · exact ⟨b, χ, hb, key.1, sameFlag_trans (tan_chart Z hb) (fun σ j => (fr.1 σ j).1) (fun σ j => (key.1.1 σ j).1)
        sf key.2⟩
    · obtain ⟨j, hj, ej⟩ := hV σ i
      have := ((hv σ i.succ).step (Nat.lt_succ_iff.1 i.succ.2) _ fu').2 j hj
      rw [e₃, ← ej, ← bc_bc] at this
      exact this
    · exact ⟨m σ, _, e σ, fun _ => rfl, ((hB' σ).bc φ).congr (Category.assoc _ _ _).symm⟩

theorem hasDR_of_allSteps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z Z' : Mdl Y i₀), (∀ σ, Z'.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ t ∈ allSteps (Lat.top Z), Step.Holds t Z') → HasDR Z' := by
  intro E _ _ _ H Dw Xo p W _ _ Y i₀ Z Z' hty h
  refine ⟨hty, fun x => exists_intFrame Z' x fun σ r => ?_⟩
  obtain ⟨U, hU, n, v, hx, h1, h2, h3⟩ := GlobalTheory.T.step_holds_local_tangent_frames E H Dw Xo p W Y i₀ Z Z' σ r (Nat.lt_succ_iff.1 r.2)
    (h _ (mem_allSteps.2 ⟨σ, r, _, rfl⟩)) x
  exact ⟨U, hU, n, v, hx, ⟨h1, h2⟩, h3⟩

end GlobalTheory.LocM.StepFrame
