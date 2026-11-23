import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineOpenRingOnEqAdjoinInv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointOfRingHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

section Specialise

variable {o Ω K J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field K] [Fintype J]

theorem map_dotProduct_of_mem {B : Subalgebra o Ω} {f : Ω → K} (φ : B →+* K) (hf : ∀ x : B, φ x = f x)
    {u v : J → Ω} (hu : ∀ j, u j ∈ B) (hv : ∀ j, v j ∈ B) :
    f (u ⬝ᵥ v) = (fun j => f (u j)) ⬝ᵥ fun j => f (v j) := by
  have h : u ⬝ᵥ v = ((∑ j, (⟨u j, hu j⟩ : B) * ⟨v j, hv j⟩ : B) : Ω) := by
    simp [dotProduct]
  rw [h, ← hf, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hf, hf]

theorem dotProduct_mem_of_mem_span {σ : Type} [SetLike σ K] [SubringClass σ K] (O : σ) {s : Set (J → K)} {w v : J → K}
    (hs : ∀ x ∈ s, w ⬝ᵥ x ∈ O) (hv : v ∈ Submodule.span O s) : w ⬝ᵥ v ∈ O := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : w ⬝ᵥ (c • x) = (c : K) * (w ⬝ᵥ x) := dotProduct_smul (c : K) w x
    rw [this]
    exact mul_mem c.2 hx

omit [Fintype J] in

theorem map_mem_span_of_mem_span {A B : Subalgebra o Ω} (hAB : A ≤ B) {f : Ω → K} (φ : B →+* K)
    (hf : ∀ x : B, φ x = f x) (O : ValuationSubring K) (hO : ∀ x ∈ A, f x ∈ O) {I : Type} {g : I → J → Ω}
    (hg : ∀ k j, g k j ∈ B) {v : J → Ω} (hv : v ∈ Submodule.span A (Set.range g)) :
    (∀ j, v j ∈ B) ∧ (fun j => f (v j)) ∈ Submodule.span O (Set.range fun k j => f (g k j)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨hg k, Submodule.subset_span ⟨k, rfl⟩⟩
  | zero =>
    refine ⟨fun _ => zero_mem B, ?_⟩
    have h0 : f 0 = 0 := (hf 0).symm.trans (map_zero φ)
    have : (fun j => f ((0 : J → Ω) j)) = 0 := funext fun _ => h0
    rw [this]
    exact zero_mem _
  | add x y _ _ hx hy =>
    refine ⟨fun j => add_mem (hx.1 j) (hy.1 j), ?_⟩
    have : (fun j => f ((x + y) j)) = (fun j => f (x j)) + fun j => f (y j) := funext fun j =>
      (hf (⟨_, hx.1 j⟩ + ⟨_, hy.1 j⟩)).symm.trans (by rw [map_add, hf, hf]; rfl)
    rw [this]
    exact add_mem hx.2 hy.2
  | smul c x _ hx =>
    refine ⟨fun j => mul_mem (hAB c.2) (hx.1 j), ?_⟩
    have : (fun j => f ((c • x) j)) = (⟨f c, hO c c.2⟩ : O) • fun j => f (x j) := funext fun j =>
      (hf (⟨_, hAB c.2⟩ * ⟨_, hx.1 j⟩)).symm.trans (by rw [map_mul, hf, hf]; rfl)
    rw [this]
    exact Submodule.smul_mem _ _ hx.2

theorem mem_span_map_iff_forall_dotProduct_mem [DecidableEq J] {A B : Subalgebra o Ω} (hAB : A ≤ B) {f : Ω → K}
    (φ : B →+* K) (hf : ∀ x : B, φ x = f x) (O : ValuationSubring K) (hO : ∀ x ∈ A, f x ∈ O) {I : Type}
    {g : I → J → Ω} (hg : ∀ k j, g k j ∈ B) (b : Matrix J J Ω)
    (hb : Submodule.span B (Set.range b) = Submodule.span B (Set.range fun i => Pi.single i (1 : Ω)))
    (H : ∀ w : J → Ω, w ∈ Submodule.span A (Set.range g) ↔ ∀ v ∈ Submodule.span A (Set.range b), w ⬝ᵥ v ∈ A)
    (w : J → K) :
    w ∈ Submodule.span O (Set.range fun k j => f (g k j)) ↔
      ∀ v ∈ Submodule.span O ((fun (v : J → Ω) j => f (v j)) '' (Submodule.span A (Set.range b))), w ⬝ᵥ v ∈ O := by
  have hbB : ∀ i j, b i j ∈ B := fun i j => by
    have h : b i ∈ Submodule.span B (Set.range fun i => (Pi.single i (1 : Ω) : J → Ω)) :=
      hb ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
    rw [← hc]
    simp [Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def]
  constructor
  · intro hw v hv
    refine dotProduct_mem_of_mem_span O ?_ hv
    rintro _ ⟨x, hx, rfl⟩
    rw [dotProduct_comm]
    refine dotProduct_mem_of_mem_span O ?_ hw
    rintro _ ⟨k, rfl⟩
    rw [dotProduct_comm, ← map_dotProduct_of_mem φ hf (hg k) (map_mem_span_of_mem_span hAB φ hf O hO hbB hx).1]
    exact hO _ ((H _).1 (Submodule.subset_span ⟨k, rfl⟩) x hx)
  · intro hw
    have h1 : ∀ i, ∃ c : J → B, ∑ l, HSMul.hSMul (c l) (b l) = (Pi.single i 1 : J → Ω) := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
    choose c hc using h1
    let d : Matrix J J Ω := Matrix.of fun i l => (c i l : Ω)
    have hd : d * b = 1 := by
      ext i j
      have := congrFun (hc i) j
      simpa [Matrix.mul_apply, d, Finset.sum_apply, Subalgebra.smul_def, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    have hd' : b * d = 1 := mul_eq_one_comm.1 hd
    have h2 : ∀ i, (fun j => d j i) ∈ Submodule.span A (Set.range g) := fun i => (H _).2 fun v hv => by
      refine dotProduct_mem_of_mem_span A ?_ hv
      rintro _ ⟨l, rfl⟩
      have : (fun j => d j i) ⬝ᵥ b l = (b * d) l i := dotProduct_comm _ _
      rw [this, hd', Matrix.one_apply]
      split_ifs
      exacts [one_mem A, zero_mem A]
    have h3 : ∀ i, w ⬝ᵥ (fun j => f (b i j)) ∈ O := fun i =>
      hw _ (Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩)
    have h4 : ∀ j l, ∑ i, f (d j i) * f (b i l) = if j = l then 1 else 0 := fun j l => by
      have h := map_dotProduct_of_mem φ hf (u := d j) (v := fun i => b i l) (fun i => (c j i).2) (fun i => hbB i l)
      have h' : d j ⬝ᵥ (fun i => b i l) = (d * b) j l := rfl
      rw [h', hd, Matrix.one_apply] at h
      refine h.symm.trans ?_
      split_ifs
      exacts [(hf 1).symm.trans (map_one φ), (hf 0).symm.trans (map_zero φ)]
    have h5 : w = ∑ i, (⟨_, h3 i⟩ : O) • fun j => f (d j i) := by
      funext j
      have : ∀ i, ((⟨_, h3 i⟩ : O) • fun j => f (d j i)) j = ∑ l, w l * (f (d j i) * f (b i l)) := fun i => by
        show (w ⬝ᵥ (fun j => f (b i j))) * f (d j i) = _
        rw [dotProduct, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [Finset.sum_apply, Finset.sum_congr rfl fun i _ => this i, Finset.sum_comm]
      simp only [← Finset.mul_sum, h4]
      simp
    rw [h5]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (map_mem_span_of_mem_span hAB φ hf O hO hg (h2 i)).2

omit [Fintype J] in

theorem mem_span_iff_div_mem_span (O : ValuationSubring K) {I : Type} (G : I → J → K) {u : K} (hu : u ≠ 0)
    (w : J → K) :
    w ∈ Submodule.span O (Set.range G) ↔ u⁻¹ • w ∈ Submodule.span O (Set.range fun k j => G k j / u) := by
  have key : ∀ (G : I → J → K) (s : K) (w : J → K), w ∈ Submodule.span O (Set.range G) →
      s • w ∈ Submodule.span O (Set.range fun k => s • G k) := fun G s w hw => by
    have := Submodule.mem_map_of_mem (f := (LinearMap.lsmul K (J → K) s).restrictScalars O) hw
    rwa [Submodule.map_span, ← Set.range_comp] at this
  have e : (fun k j => G k j / u) = fun k => u⁻¹ • G k := by
    funext k j
    simp [div_eq_inv_mul]
  rw [e]
  refine ⟨key G _ w, fun h => ?_⟩
  simpa [smul_smul, hu] using key _ u _ h

end Specialise

theorem exists_generators_at_all_tests : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG₀ : Fin n → S.J → S.R), S.Over₀ M U₀ → IsAffineOpen U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → S.IsEE M U₀ EE → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => (GG₀ k j : Ω) / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ (R' : Subalgebra o Ω) (hR : S.R ≤ R') (GG : Fin n → S.J → R'), R'.FG ∧ (∀ k j, (GG k j : Ω) = GG₀ k j) ∧ (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) := by
  intro o Ω _ _ _ _ S M U₀ EE n a GG₀ hO hU hsupp hEE hgen
  refine ⟨M.ringOn U₀, hO.le, fun k j => ⟨GG₀ k j, hO.le (GG₀ k j).2⟩, RatModel.fg_ringOn hU hO.ne,
    fun _ _ => rfl, fun p _ y' τ hy' w => ?_⟩
  obtain ⟨z, y, hz, hv⟩ := RatModel.exists_cen_of_ringHom o Ω M U₀ (projProper _ _ _ hO.proj) hU hO.ne p y' hy'
  have hAt : S.At M y (y'.comp (Subalgebra.inclusion hO.le).toRingHom) := fun r => hv ⟨r, hO.le r.2⟩
  obtain ⟨x₀, hx₀⟩ := hO.div z
  have hδ := ((hsupp z p y _ τ hz hAt).1 x₀).1 hx₀
  obtain ⟨V, b, hzV, -, hb⟩ := EE.loc z
  let ξ : M.Z := (gPt p ≫ y) (IsLocalRing.closedPoint _)
  have hξ : ξ ⤳ z := RatModel.gPt_specializes hz.1 _
  have hξU : ξ ∈ U₀ := hz.2 ⟨_, rfl⟩
  have hle : M.ringOn U₀ ≤ M.O ξ := RatModel.ringOn_le_O hξU
  let φ := RatModel.valHom (gPt p ≫ y) ξ (RatModel.range_eq_singleton _ _)
  have ht : S.th x₀ ∈ M.O ξ := hle (hO.le (S.th_mem x₀))
  have ht' : (S.th x₀)⁻¹ ∈ M.O ξ := hle (hO.th_unit x₀ hx₀.1)
  have hg : ∀ k j, (GG₀ k j : Ω) / S.th x₀ ^ a ∈ M.O ξ := fun k j => by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (hle (hO.le (GG₀ k j).2)) (pow_mem ht' a)
  have H := hgen z x₀ hx₀
  have hE := hEE.2 z p y _ τ hz hAt
  rw [hb z hzV] at H hE
  have key := mem_span_map_iff_forall_dotProduct_mem (RatModel.O_le_of_specializes hξ) φ (fun _ => rfl) (OO p)
    (fun x hx => (mem_OO_iff _).2 (RatModel.norm_val_le_one hz.1 hx)) hg b
    ((hb ξ (hξ.mem_open V.isOpen hzV)).symm.trans (hEE.1 ξ hξU)) H
  set u := M.val (gPt p ≫ y) (S.th x₀) with hu
  have hu0 : u ^ a ≠ 0 := pow_ne_zero _ (norm_pos_iff.1 (hδ ▸ τ.δ_pos))
  have e : (fun k j => y' ⟨GG₀ k j, hO.le (GG₀ k j).2⟩ / u ^ a) =
      fun k j => M.val (gPt p ≫ y) ((GG₀ k j : Ω) / S.th x₀ ^ a) := by
    funext k j
    rw [div_eq_iff hu0, hv]
    have h := map_mul φ ⟨_, hg k j⟩ (⟨_, ht⟩ ^ a)
    rw [map_pow] at h
    refine Eq.trans ?_ h
    exact congrArg (M.val (gPt p ≫ y)) (div_mul_cancel₀ _ (pow_ne_zero a hx₀.1)).symm
  rw [mem_span_iff_div_mem_span (OO p) _ hu0, e]
  refine (key _).trans ?_
  rw [← hE]
  refine forall₂_congr fun v _ => ?_
  rw [mem_OO_iff, smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, norm_pow, hδ,
    inv_mul_le_iff₀ (pow_pos τ.δ_pos a), _root_.mul_one]

end GlobalTheory.ZH
end
