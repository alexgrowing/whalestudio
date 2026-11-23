import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphericalSpan

variable {G V : Type} [Group G]

theorem finite_range_of_relIndex {X : Type} (H K : Subgroup G) (hne : H.relIndex K ≠ 0) (f : K → X)
    (hf : ∀ k h : K, (h : G) ∈ H → f (k * h) = f k) : (Set.range f).Finite := by
  have : (H.subgroupOf K).FiniteIndex := ⟨hne⟩
  refine (Set.finite_range (fun q : K ⧸ H.subgroupOf K => f (Quotient.out q))).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf K) k
  refine ⟨(k : K ⧸ H.subgroupOf K), ?_⟩
  show f (Quotient.out (k : K ⧸ H.subgroupOf K)) = f k
  rw [hh]
  exact hf k h (Subgroup.mem_subgroupOf.1 h.2)

theorem doset_finite (K : Subgroup G) (hc : IsCommensurated K) (g : G) :
    {q : G ⧸ K | Quotient.out q ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)}.Finite := by
  have hfin := finite_range_of_relIndex (Subgroup.map (MulAut.conj g).toMonoidHom K) K (hc g)
    (fun k : K => ((k * g : G) : G ⧸ K)) (by
      rintro k h hh
      obtain ⟨b, hb, e⟩ := Subgroup.mem_map.1 hh
      have e' : (h : G) = g * b * g⁻¹ := by simpa using e.symm
      refine QuotientGroup.eq.2 ?_
      have : ((k : G) * (h : G) * g)⁻¹ * ((k : G) * g) = b⁻¹ := by
        rw [e']; group
      show (((k * h : K) : G) * g)⁻¹ * ((k : G) * g) ∈ K
      rw [Subgroup.coe_mul, this]
      exact K.inv_mem hb)
  refine hfin.subset ?_
  intro q hq
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hq
  refine ⟨⟨a, ha⟩, ?_⟩
  have h1 : ((Quotient.out q : G) : G ⧸ K) = q := QuotientGroup.out_eq' q
  rw [← h1, e]
  refine QuotientGroup.eq.2 ?_
  have : (a * g)⁻¹ * (a * g * b) = b := by group
  show (a * g)⁻¹ * (a * g * b) ∈ K
  rw [this]
  exact hb

theorem dosetInd_mem_hecke (K : Subgroup G) (g : G) : dosetInd ℂ K g ∈ Hecke ℂ K := by
  classical
  have hmem : ∀ (a b : K) (s : G), (a * s * b : G) ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      s ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
    intro a b s
    constructor
    · intro h
      obtain ⟨c, hc, d, hd, e⟩ := DoubleCoset.mem_doubleCoset.1 h
      refine DoubleCoset.mem_doubleCoset.2 ⟨(a : G)⁻¹ * c, K.mul_mem (K.inv_mem a.2) hc,
        d * (b : G)⁻¹, K.mul_mem hd (K.inv_mem b.2), ?_⟩
      have : s = (a : G)⁻¹ * ((a : G) * s * b) * (b : G)⁻¹ := by group
      rw [this, e]; group
    · intro h
      obtain ⟨c, hc, d, hd, e⟩ := DoubleCoset.mem_doubleCoset.1 h
      exact DoubleCoset.mem_doubleCoset.2 ⟨a * c, K.mul_mem a.2 hc, d * b, K.mul_mem hd b.2, by
        rw [e]; group⟩
  refine ⟨?_, {g}, ?_⟩
  · intro a b s
    by_cases hs : s ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)
    · simp [dosetInd, Set.indicator_of_mem hs, Set.indicator_of_mem ((hmem a b s).2 hs)]
    · simp [dosetInd, Set.indicator_of_notMem hs,
        Set.indicator_of_notMem (fun h => hs ((hmem a b s).1 h))]
  · intro s hs
    have : s ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
      by_contra h
      exact hs (by simp [dosetInd, Set.indicator_of_notMem h])
    obtain ⟨c, hc, d, hd, e⟩ := DoubleCoset.mem_doubleCoset.1 this
    exact ⟨g, by simp, ⟨c, hc⟩, ⟨d, hd⟩, e⟩

variable [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := (show ∀ h : K, ρ h v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v from h) ⟨k, hk⟩
    simpa using this
  · intro h
    exact (show ∀ h : K, ρ h v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v from fun k => by
      simpa using h k k.2)

theorem pairing_translate_eq_zero (ρ : Representation ℂ G V) (K : Subgroup G)
    (hc : IsCommensurated K) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w) {x y : V}
    (hx : ∀ k ∈ K, ρ k x = x) (hy : ∀ k ∈ K, ρ k y = y)
    (hE : ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec ρ K h x = c • x) (hyx : B y x = 0) (g : G) :
    B y (ρ g x) = 0 := by
  classical
  obtain ⟨c, hc'⟩ := hE _ (dosetInd_mem_hecke K g)
  have hfin := doset_finite K hc g
  have hS : ∀ q, q ∈ hfin.toFinset ↔
      Quotient.out q ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
    intro q; simp
  have hsum : heckeVec ρ K (dosetInd ℂ K g) x = ∑ q ∈ hfin.toFinset, ρ (Quotient.out q) x := by
    unfold heckeVec
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      have h1 := (hS q).1 hq
      simp [dosetInd, Set.indicator_of_mem h1]
    · intro q hq
      rw [Finset.mem_coe, hS]
      by_contra h
      exact hq (by simp [dosetInd, Set.indicator_of_notMem h])
  have hterm : ∀ q ∈ hfin.toFinset, B y (ρ (Quotient.out q) x) = B y (ρ g x) := by
    intro q hq
    obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 ((hS q).1 hq)
    have h1 : ρ (Quotient.out q) x = ρ a (ρ g x) := by
      rw [e, map_mul, map_mul]
      simp [hx b hb]
    rw [h1]
    calc B y (ρ a (ρ g x)) = B (ρ a y) (ρ a (ρ g x)) := by rw [hy a ha]
      _ = B y (ρ g x) := hB a _ _
  have hne : (g : G ⧸ K) ∈ hfin.toFinset := by
    rw [hS]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hh]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, h, h.2, by simp⟩
  have h0 : B y (c • x) = 0 := by simp [hyx]
  rw [← hc', hsum, map_sum, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at h0
  have hcard : ((hfin.toFinset.card : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, hne⟩)
  exact (mul_eq_zero.1 h0).resolve_left hcard

theorem exists_open_fix [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hc : IsCommensurated K) {x : V}
    (hx : ∀ k ∈ K, ρ k x = x) {y : V}
    (hy : y ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x)) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ H.relIndex K ≠ 0 ∧ ∀ h ∈ H, ρ h y = y := by
  induction hy using Submodule.span_induction with
  | mem y h =>
    obtain ⟨g, rfl⟩ := h
    refine ⟨Subgroup.map (MulAut.conj g).toMonoidHom K, ?_, hc g, ?_⟩
    · have : ((Subgroup.map (MulAut.conj g).toMonoidHom K : Subgroup G) : Set G) =
          (fun h : G => g⁻¹ * h * g) ⁻¹' (K : Set G) := by
        ext h
        simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
        constructor
        · rintro ⟨k, hk, rfl⟩
          have : g⁻¹ * (MulAut.conj g).toMonoidHom k * g = k := by simp [mul_assoc]
          rw [this]; exact hk
        · intro hk
          exact ⟨_, hk, by simp [mul_assoc]⟩
      rw [this]
      exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · intro h hh
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hh
      have e : (MulAut.conj g).toMonoidHom k = g * k * g⁻¹ := by simp
      have : ρ (g * k * g⁻¹) (ρ g x) = ρ g (ρ k x) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        simp
      rw [e, this, hx k hk]
  | zero => exact ⟨⊤, isOpen_univ, by simp, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨H₁, o₁, i₁, f₁⟩ := ha
    obtain ⟨H₂, o₂, i₂, f₂⟩ := hb
    refine ⟨H₁ ⊓ H₂, o₁.inter o₂, Subgroup.relIndex_inf_ne_zero i₁ i₂, fun h hh => ?_⟩
    rw [map_add, f₁ h hh.1, f₂ h hh.2]
  | smul a b _ hb =>
    obtain ⟨H, o, i, f⟩ := hb
    exact ⟨H, o, i, fun h hh => by rw [map_smul, f h hh]⟩

theorem pairing_span_eq_zero (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {x y w : V}
    (hy : ∀ g, B y (ρ g x) = 0) (hw : w ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x)) :
    B y w = 0 := by
  induction hw using Submodule.span_induction with
  | mem w h => obtain ⟨g, rfl⟩ := h; exact hy g
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b _ hb => simp [hb]

theorem fixed_eq_smul (ρ : Representation ℂ G V) (K : Subgroup G)
    (hc : IsCommensurated K) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hpos : ∀ v : V, v ≠ 0 → 0 < (B v v).re)
    (hB : ∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w) {x y : V} (hx0 : x ≠ 0)
    (hx : ∀ k ∈ K, ρ k x = x) (hE : ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec ρ K h x = c • x)
    (hyU : y ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x)) (hy : ∀ k ∈ K, ρ k y = y) :
    ∃ c : ℂ, y = c • x := by
  have hxx : B x x ≠ 0 := fun h => by
    have := hpos x hx0
    simp [h] at this
  have hxU : x ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x) :=
    Submodule.subset_span ⟨1, by simp⟩
  refine ⟨B y x / B x x, ?_⟩
  set c := B y x / B x x with hcdef
  have hz : B (y - c • x) x = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hcdef]
    field_simp
    ring
  have hzf : ∀ k ∈ K, ρ k (y - c • x) = y - c • x := by
    intro k hk
    rw [map_sub, map_smul, hy k hk, hx k hk]
  have hzU : y - c • x ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x) :=
    Submodule.sub_mem _ hyU (Submodule.smul_mem _ _ hxU)
  have hzz : B (y - c • x) (y - c • x) = 0 :=
    pairing_span_eq_zero ρ B (pairing_translate_eq_zero ρ K hc B hB hx hzf hE hz) hzU
  by_contra hne
  have := hpos (y - c • x) (sub_ne_zero.2 hne)
  rw [hzz] at this
  simp at this

theorem mem_of_invariant [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hc : IsCommensurated K)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v : V, v ≠ 0 → 0 < (B v v).re)
    (hB : ∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w) {x y : V} (hx0 : x ≠ 0)
    (hx : ∀ k ∈ K, ρ k x = x) (hE : ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec ρ K h x = c • x)
    (W : Submodule ℂ V) (hWU : W ≤ Submodule.span ℂ (Set.range fun g : G => ρ g x))
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) (hyW : y ∈ W) (hy0 : y ≠ 0) : x ∈ W := by
  classical
  have hex : ∃ g, B y (ρ g x) ≠ 0 := by
    by_contra hno
    push Not at hno
    have := hpos y hy0
    simp [pairing_span_eq_zero ρ B hno (hWU hyW)] at this
  obtain ⟨g, hg⟩ := hex
  have hgi : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hy1W : ρ g⁻¹ y ∈ W := hW _ _ hyW
  have hy1x : B (ρ g⁻¹ y) x ≠ 0 := by
    rw [← hB g, hgi]; exact hg
  generalize ρ g⁻¹ y = y₁ at hy1W hy1x
  obtain ⟨H, -, hi, hf⟩ := exists_open_fix ρ K hKo hc hx (hWU hy1W)
  have hfin := finite_range_of_relIndex H K hi (fun k : K => ρ k y₁) (by
    intro k h hh
    show ρ ((k * h : K) : G) y₁ = ρ k y₁
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hf h hh])
  have hF : ∀ u, u ∈ hfin.toFinset ↔ ∃ k : K, ρ k y₁ = u := by
    intro u; simp
  have hzW : ∑ u ∈ hfin.toFinset, u ∈ W := by
    refine Submodule.sum_mem _ fun u hu => ?_
    obtain ⟨k, rfl⟩ := (hF u).1 hu
    exact hW _ _ hy1W
  have hzf : ∀ k ∈ K, ρ k (∑ u ∈ hfin.toFinset, u) = ∑ u ∈ hfin.toFinset, u := by
    intro k hk
    rw [map_sum]
    refine Finset.sum_nbij' (ρ k) (ρ k⁻¹) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro u hu
      obtain ⟨l, rfl⟩ := (hF u).1 hu
      refine (hF _).2 ⟨⟨k, hk⟩ * l, ?_⟩
      simp [map_mul]
    · intro u hu
      obtain ⟨l, rfl⟩ := (hF u).1 hu
      refine (hF _).2 ⟨⟨k⁻¹, K.inv_mem hk⟩ * l, ?_⟩
      simp [map_mul]
    · intro u _
      rw [← Module.End.mul_apply, ← map_mul]; simp
    · intro u _
      rw [← Module.End.mul_apply, ← map_mul]; simp
  obtain ⟨c, hcz⟩ := fixed_eq_smul ρ K hc B hpos hB hx0 hx hE (hWU hzW) hzf
  have hterm : ∀ u ∈ hfin.toFinset, B u x = B y₁ x := by
    intro u hu
    obtain ⟨k, rfl⟩ := (hF u).1 hu
    calc B (ρ k y₁) x = B (ρ k y₁) (ρ k x) := by rw [hx k k.2]
      _ = B y₁ x := hB _ _ _
  have hmem : y₁ ∈ hfin.toFinset := (hF _).2 ⟨1, by simp⟩
  have hBz : B (∑ u ∈ hfin.toFinset, u) x ≠ 0 := by
    rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, hmem⟩)) hy1x
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hBz
    rw [hcz]; simp
  have : x = c⁻¹ • ∑ u ∈ hfin.toFinset, u := by
    rw [hcz, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]
  exact W.smul_mem _ hzW

end GlobalTheory.SphericalSpan

open GlobalTheory.SphericalSpan in

theorem GlobalTheory.spherical_eigenvector_generates_irreducible :
    ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
      [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) →
      IsCommensurated K → IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ K →
      (∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec ρ K h x = c • x) →
      ∃ (U : Submodule ℂ V) (hU : ∀ g, ∀ y ∈ U, ρ g y ∈ U) (hx : x ∈ U),
        IsIrrSmooth (GlobalTheory.PRep.sub ρ U hU) ∧ IsUnitarisable (GlobalTheory.PRep.sub ρ U hU) ∧
        ∀ y ∈ fixed (GlobalTheory.PRep.sub ρ U hU) K, ∃ c : ℂ, y = c • (⟨x, hx⟩ : U) := by
  intro G V _ _ _ _ _ ρ K hKo hc hun x hx0 hxf hE
  obtain ⟨B, hsym, hpos, hB⟩ := hun
  have hxK : ∀ k ∈ K, ρ k x = x := mem_fixed_iff.1 hxf
  have hUinv : ∀ g, ∀ y ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x),
      ρ g y ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x) := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem y h =>
      obtain ⟨a, rfl⟩ := h
      exact Submodule.subset_span ⟨g * a, by simp [map_mul]⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [map_smul]; exact Submodule.smul_mem _ _ hb
  have hxU : x ∈ Submodule.span ℂ (Set.range fun g : G => ρ g x) :=
    Submodule.subset_span ⟨1, by simp⟩
  refine ⟨_, hUinv, hxU, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    intro v
    obtain ⟨H, ho, -, hf⟩ := exists_open_fix ρ K hKo hc hxK v.2
    let S : Subgroup G :=
      { carrier := {g | GlobalTheory.PRep.sub ρ _ hUinv g v = v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]; simp }
    have hle : H ≤ S := by
      intro h hh
      exact Subtype.ext (hf h hh)
    exact Subgroup.isOpen_mono hle ho
  ·
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := ?_ }
    · have h1 : (⟨x, hxU⟩ : Submodule.span ℂ (Set.range fun g : G => ρ g x)) ∈
          (⊤ : Subrepresentation (GlobalTheory.PRep.sub ρ _ hUinv)).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      have h2 : (⟨x, hxU⟩ : Submodule.span ℂ (Set.range fun g : G => ρ g x)) = 0 :=
        (Submodule.mem_bot ℂ).1 h1
      exact hx0 (congrArg Subtype.val h2)
    · intro S
      by_cases hS : S.toSubmodule = ⊥
      · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
      · right
        apply Subrepresentation.toSubmodule_injective
        obtain ⟨y, hyS, hy0⟩ := (Submodule.ne_bot_iff _).1 hS
        let W : Submodule ℂ V := S.toSubmodule.map (Submodule.subtype _)
        have hWU : W ≤ Submodule.span ℂ (Set.range fun g : G => ρ g x) := by
          rintro _ ⟨u, -, rfl⟩
          exact u.2
        have hWinv : ∀ g, ∀ v ∈ W, ρ g v ∈ W := by
          rintro g _ ⟨u, hu, rfl⟩
          exact ⟨_, S.apply_mem_toSubmodule g hu, rfl⟩
        have hxW : x ∈ W := mem_of_invariant ρ K hKo hc B hpos hB hx0 hxK hE W hWU hWinv
          (y := y) ⟨y, hyS, rfl⟩ (fun h => hy0 (Subtype.ext h))
        have hall : Submodule.span ℂ (Set.range fun g : G => ρ g x) ≤ W :=
          Submodule.span_le.2 (by
            rintro _ ⟨g, rfl⟩
            exact hWinv g x hxW)
        refine eq_top_iff.2 fun u _ => ?_
        obtain ⟨u', hu', e⟩ := hall u.2
        have : u' = u := Subtype.ext e
        exact this ▸ hu'
  ·
    refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => B a b)
      (by intro a b c; simp) (by intro r a b; simp) (by intro a b c; simp)
      (by intro r a b; simp), ?_, ?_, ?_⟩
    · intro v w
      exact hsym v w
    · intro v hv
      exact hpos v (fun h => hv (Subtype.ext h))
    · intro g v w
      exact hB g v w
  · intro y hy
    have hyK : ∀ k ∈ K, ρ k y = y := fun k hk =>
      congrArg Subtype.val (mem_fixed_iff.1 hy k hk)
    obtain ⟨c, hcy⟩ := fixed_eq_smul ρ K hc B hpos hB hx0 hxK hE y.2 hyK
    exact ⟨c, Subtype.ext hcy⟩
