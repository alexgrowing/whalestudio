import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZhStable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ)

theorem act_natCast (m : ℕ) : Xo.univ.t.act.act m = 𝟙 Xo.univ.t.G ^ m := by
  induction m with
  | zero =>
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]; exact mul_eq_left.1 h.symm
  | succ m ih => rw [Nat.cast_succ, Xo.univ.t.act.add, ih, Xo.univ.t.act.one, pow_succ]

theorem comp_list_prod {T T' : Over Xo.X} (h : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map fun x => h ≫ x).prod = h ≫ L.prod := by
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.prod_nil, MonObj.comp_one]
  | cons x L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem inZh_comp {T T' : Over Xo.X} (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) :
    InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := comp_list_prod Xo h (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j))
    rw [ha.2 mu hmu cm hcm i, MonObj.comp_one, List.map_ofFn] at h1
    simpa only [Function.comp_def, Category.assoc] using h1

theorem inZh_mul {T : Over Xo.X} (a a' : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a)
    (ha' : InZh Xo Λ N a') : InZh Xo Λ N (fun b => a b * a' b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [mul_pow, ha.1 b, ha'.1 b, _root_.mul_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have h2 := ha'.2 mu hmu cm hcm i
    rw [List.prod_ofFn] at h1 h2 ⊢
    have h3 : ∀ j, (a j * a' j) ≫ Xo.univ.t.act.act (cm i j) =
        (a j ≫ Xo.univ.t.act.act (cm i j)) * (a' j ≫ Xo.univ.t.act.act (cm i j)) := fun j => by
      have := Xo.univ.t.act.hom (cm i j)
      exact MonObj.mul_comp _ _ _
    simp only [h3]
    rw [Finset.prod_mul_distrib, h1, h2, _root_.mul_one]

theorem geoInj_comp {S T : Type} [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X)
    (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ) {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hz : GeoInj Xo x0 z) :
    GeoInj Xo x1 (fun i b => h ≫ z i b) := by
  intro k _ χ g hg i j hij
  let g' : ptO Xo (spMap (χ.comp ψ) ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap (χ.comp ψ)) rfl
  have hc : spMap (χ.comp ψ) = g.left ≫ h.left := by
    rw [hg, hh]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine hz k (χ.comp ψ) g' rfl (funext fun b => Over.OverMorphism.ext ?_)
  have h1 := congrArg (fun f => f.left) (congrFun hij b)
  change spMap (χ.comp ψ) ≫ (z i b).left = spMap (χ.comp ψ) ≫ (z j b).left
  rw [hc]
  simpa only [Over.comp_left, Category.assoc] using h1

theorem inZh_of_killedBy (hΛ : Λ.TrivAt l.M) {T : Over Xo.X} (u : Fin n → (T ⟶ Xo.univ.t.G))
    (hu : ∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) : InZh Xo Λ N u := by
  classical
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [pow_two, pow_mul, (hu b).1, one_pow]
  · obtain ⟨k, hk, -, hk2⟩ := hΛ
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨hN, e, he⟩ := hu j
    have hv : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.La := by
      refine hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ?_)
      intro b _
      by_cases hb : b = j
      · subst hb; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne hb]; exact Submodule.zero_mem _
    obtain ⟨m, hm⟩ := Submodule.mem_one.1 (hmu _ hv i (Set.mem_univ i))
    have hm' : (m : E) = (k : E) * mu i j := by
      have : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = (k : E) • (Pi.single j (1 : E) : Fin n → E) := by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rw [this, Matrix.mulVec_smul, Matrix.mulVec_single_one] at hm
      exact hm
    have hcmk : cm i j * k = N * m := by
      apply RingOfIntegers.ext
      have h1 : ((cm i j * k : 𝓞 E) : E) = (cm i j : E) * (k : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      have h2 : ((N * m : 𝓞 E) : E) = (N : E) * (m : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      rw [h1, h2, hcm, hm']; ring
    have hM : (l.M : 𝓞 E) ∈ l.Mb := by
      have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
        rw [l.prod]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_inf h1).1
    have hcop : IsCoprime (k : 𝓞 E) ((l.M : 𝓞 E) ^ e) := (Nat.Coprime.cast hk).pow_right
    obtain ⟨p, q, hpq⟩ := hcop
    have hsplit : cm i j = N * (m * p) + (cm i j * q) * (l.M : 𝓞 E) ^ e := by
      linear_combination (-cm i j) * hpq + p * hcmk
    have := Xo.univ.t.act.hom (m * p)
    show u j ≫ Xo.univ.t.act.act (cm i j) = 1
    rw [hsplit, Xo.univ.t.act.add, MonObj.comp_mul,
      he _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hM e)), _root_.mul_one, Xo.univ.t.act.mul,
      ← Category.assoc, act_natCast, MonObj.comp_pow, Category.comp_id, hN, MonObj.one_comp]

end GlobalTheory.ZhStable

namespace GlobalTheory

theorem inZh_geoInj_stable :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N (fun b => h ≫ a b)) ∧ (∀ (T : Over Xo.X) (a a' : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N a' → InZh Xo Λ N (fun b => a b * a' b)) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ (J : Type) (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)), GeoInj Xo x0 z → GeoInj Xo x1 (fun i b => h ≫ z i b)) ∧ (Λ.TrivAt l.M → ∀ (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) → InZh Xo Λ N u) :=
  fun _ _ _ _ _ _ _ Xo _ Λ N =>
    ⟨fun _ _ h a => ZhStable.inZh_comp Xo Λ N h a, fun _ a a' => ZhStable.inZh_mul Xo Λ N a a',
      fun _ _ _ _ x0 x1 ψ h hh _ z => ZhStable.geoInj_comp Xo x0 x1 ψ h hh z,
      fun hΛ _ u => ZhStable.inZh_of_killedBy Xo Λ N hΛ u⟩

end GlobalTheory
