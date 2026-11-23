import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitMove
variable {D : D7}

def intSub (D : D7) (n : ℕ) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) where
  carrier := intVec D n
  add_mem' := fun ha hb k => (ha k).add (hb k)
  zero_mem' := fun _ => isIntegral_zero
  smul_mem' := fun c x hx k => by
    show IsIntegral ℤ ((c : D.host.E) * x k)
    exact (RingOfIntegers.isIntegral_coe c).mul (hx k)

theorem coe_intSub (n : ℕ) : ((intSub D n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := rfl

set_option maxHeartbeats 1000000 in
theorem hat_intVec_iff (D : D7) (n : ℕ) (z : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E) :
    z ∈ GlobalTheory.AdLat.hat D.host.F (intVec D n) ↔
      ∀ i, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E (z i) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set cm := Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E

  have mono : ∀ m ∈ Submonoid.closure ((Set.range fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∪
      Set.range fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Formalism.L2.Herm.Af D.host.F)),
      ∃ x : D.host.E, IsIntegral ℤ x ∧ ∃ a : Formalism.L2.Herm.Af D.host.F, a ∈ Formalism.UG.intAd D.host.F ∧ m = x ⊗ₜ[D.host.F] a := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      rcases hm with ⟨⟨x, b, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
      · exact ⟨algebraMap (𝓞 D.host.E) D.host.E b, RingOfIntegers.isIntegral_coe b, 1, one_mem _, rfl⟩
      · exact ⟨1, isIntegral_one, y, hy, rfl⟩
    | one => exact ⟨1, isIntegral_one, 1, one_mem _, rfl⟩
    | mul m m' _ _ h h' =>
      obtain ⟨x, hx, a, ha, rfl⟩ := h
      obtain ⟨x', hx', a', ha', rfl⟩ := h'
      exact ⟨x * x', hx.mul hx', a * a', mul_mem ha ha', by rw [Algebra.TensorProduct.tmul_mul_tmul]⟩
  have single : ∀ (i : Fin n) (t : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F), t ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
      Pi.single i (cm.symm t) ∈ GlobalTheory.AdLat.hat D.host.F (intVec D n) := by
    intro i t ht
    rw [Formalism.L2.Herm.intAf, Formalism.UG.tensInt, Subring.mem_closure_iff] at ht
    induction ht using AddSubgroup.closure_induction with
    | mem m hm =>
      obtain ⟨x, hx, a, ha, rfl⟩ := mono m hm
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i x, fun k => ?_, ?_⟩
      · by_cases hk : k = i
        · subst hk; simpa using hx
        · rw [Pi.single_eq_of_ne hk]; exact isIntegral_zero
      · funext k
        by_cases hk : k = i
        · subst hk; simp [cm]
        · simp [Pi.single_eq_of_ne hk]
    | zero => simp
    | add s t _ _ hs ht => rw [map_add, Pi.single_add]; exact add_mem hs ht
    | neg s _ hs => rw [map_neg, Pi.single_neg]; exact neg_mem hs
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      intro i
      have : cm (a ⊗ₜ[D.host.F] x i) = (x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        simp [cm, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this]
      refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨x i, ⟨⟨x i, hx i⟩, rfl⟩⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => intro i; simp
    | add s t _ _ hs ht => intro i; rw [Pi.add_apply, map_add]; exact add_mem (hs i) (ht i)
    | neg s _ hs => intro i; rw [Pi.neg_apply, map_neg]; exact neg_mem (hs i)
  · intro hz
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have h1 := single i _ (hz i)
    rwa [AlgEquiv.symm_apply_apply] at h1

theorem dual_intVec (D : D7) (n : ℕ) (v : Fin n → D.host.E) :
    (∀ y ∈ intVec D n, ∑ a, ∑ b, v a * (1 : Matrix (Fin n) (Fin n) D.host.E) a b * GlobalTheory.Member.cF D (y b) ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ intVec D n := by
  have es : ∀ y : Fin n → D.host.E, ∑ a, ∑ b, v a * (1 : Matrix (Fin n) (Fin n) D.host.E) a b * GlobalTheory.Member.cF D (y b) =
      ∑ a, v a * GlobalTheory.Member.cF D (y a) := fun y => by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Matrix.one_apply]
  have mem : ∀ x : D.host.E, x ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔ IsIntegral ℤ x := by
    intro x
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨b, rfl⟩; exact RingOfIntegers.isIntegral_coe b
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  simp only [es, mem]
  constructor
  · intro h i
    have hi := h (Pi.single i 1) (fun k => by
      by_cases hk : k = i
      · subst hk; simp only [Pi.single_eq_same]; exact isIntegral_one
      · rw [Pi.single_eq_of_ne hk]; exact isIntegral_zero)
    have e : ∑ a, v a * GlobalTheory.Member.cF D ((Pi.single i (1 : D.host.E) : Fin n → D.host.E) a) = v i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [e] at hi
    exact hi
  · intro hv y hy
    refine IsIntegral.sum _ fun a _ => (hv a).mul ?_
    exact (hy a).map ((GlobalTheory.Member.cF D : D.host.E →+* D.host.E).toIntAlgHom)

theorem intSub_fg (n : ℕ) : (intSub D n).FG := by
  let φ : (Fin n → 𝓞 D.host.E) →ₗ[𝓞 D.host.E] (Fin n → D.host.E) :=
    LinearMap.pi fun i => (Algebra.linearMap (𝓞 D.host.E) D.host.E).comp (LinearMap.proj i)
  have e : intSub D n = Submodule.map φ ⊤ := by
    ext x
    constructor
    · intro hx
      refine ⟨fun i => ⟨x i, hx i⟩, trivial, ?_⟩
      funext i; rfl
    · rintro ⟨y, -, rfl⟩ i
      exact RingOfIntegers.isIntegral_coe (y i)
  rw [e]
  exact (Module.Finite.fg_top (R := 𝓞 D.host.E) (M := Fin n → 𝓞 D.host.E)).map φ

theorem intSub_span (n : ℕ) : Submodule.span D.host.E (intSub D n : Set (Fin n → D.host.E)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (Pi.basisFun D.host.E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩ k
  rw [Pi.basisFun_apply]
  by_cases h : i = k
  · subst h; simp only [Pi.single_eq_same]; exact isIntegral_one
  · rw [Pi.single_eq_of_ne' h]; exact isIntegral_zero

instance intSub_isLattice (n : ℕ) : Submodule.IsLattice D.host.E (intSub D n) := ⟨intSub_fg n, intSub_span n⟩

theorem sum_swap_one (n : ℕ) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * (1 : Matrix (Fin n) (Fin n) D.host.E) i j * y j =
      ∑ a, ∑ b, y a * (1 : Matrix (Fin n) (Fin n) D.host.E) a b * GlobalTheory.Member.cF D (x b) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change star (x b) * (1 : Matrix (Fin n) (Fin n) D.host.E) b a * y a = y a * (1 : Matrix (Fin n) (Fin n) D.host.E) a b * star (x b)
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp; ring
  · simp [h, Ne.symm h]

theorem selfDual_int (V : HSp D) (hV : V.gram = 1) : IsSelfDualC V (intSub D V.rank) := by
  refine ⟨inferInstance, fun y => ?_⟩
  rw [hV]
  rw [← SetLike.mem_coe, coe_intSub, ← dual_intVec D V.rank y]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [sum_swap_one, FractionalIdeal.mem_one_iff]

theorem latOf_eq (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hN : Moves V rfl g N) :
    (N : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (intVec D V.rank) := by
  have inv : ∀ y, (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  have inv' : ∀ y, (finHom V g).1 *ᵥ ((finHom V g⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec]
  have ent : ∀ (x : Fin V.rank → D.host.E) i,
      Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E
        (((finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x) i) =
      (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    intro x i
    simp only [GlobalTheory.AdForm.finM, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.reindex_apply,
      finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
  ext x
  change x ∈ N ↔ GlobalTheory.AdLat.fv D.host.F x ∈ (finHom V g).1.mulVec '' _
  rw [hN x]
  constructor
  · intro hx
    refine ⟨(finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x, (hat_intVec_iff D V.rank _).2 fun i => ?_, inv' _⟩
    rw [ent]; exact hx i
  · rintro ⟨y, hy, hxy⟩ i
    rw [← ent, ← hxy, inv]
    exact (hat_intVec_iff D V.rank y).1 hy i

theorem exists_eq_latOf (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hN : Moves V rfl g N) : N.FG ∧ Submodule.span D.host.E (N : Set (Fin V.rank → D.host.E)) = ⊤ ∧
      (GlobalTheory.AdLat.hat D.host.F (N : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E)) =
        (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (intVec D V.rank)) := by
  obtain ⟨Λ, hΛ, hfg, hsp, hhat⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (intSub D V.rank)
    (finHom V g) (intSub_fg _) (intSub_span _)
  obtain rfl : Λ = N := SetLike.coe_injective (hΛ.trans (latOf_eq V g N hN).symm)
  exact ⟨hfg, hsp, hhat⟩

theorem hat_move (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hN : Moves V rfl g N) :
    (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (intSub D V.rank : Set (Fin V.rank → D.host.E)),
      (finHom V g).1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (N : Set (Fin V.rank → D.host.E))) ∧
    (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (N : Set (Fin V.rank → D.host.E)),
      (finHom V g⁻¹).1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (intSub D V.rank : Set (Fin V.rank → D.host.E))) := by
  obtain ⟨-, -, hh⟩ := exists_eq_latOf V g N hN
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [← SetLike.mem_coe, hh]; exact ⟨z, hz, rfl⟩
  · rw [← SetLike.mem_coe, hh] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
    exact hy

theorem selfDual_move (V : HSp D) (hV : V.gram = 1) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hN : Moves V rfl g N) : IsSelfDualC V N := by
  obtain ⟨hfg, hsp, -⟩ := exists_eq_latOf V g N hN
  refine ⟨⟨hfg, hsp⟩, fun y => ?_⟩
  obtain ⟨-, -, -, -, c2, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hU := GlobalTheory.RepsCompare.isUnA_gf V (Formalism.IndefR.FWT.fin V g)
  rw [hV, Matrix.transpose_one] at hU
  have key := GlobalTheory.AdLat.latOf_selfDual D.host.F D.host.E V.rank (intSub D V.rank) (GlobalTheory.Member.cF D) 1 1 (finHom V g)
    (intSub_fg _) (intSub_span _) c2 (fun a b => by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]) (by simp) one_ne_zero (fun v => dual_intVec D V.rank v) hU
  rw [coe_intSub, ← latOf_eq V g N hN] at key
  rw [hV, ← SetLike.mem_coe, ← key y]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [sum_swap_one, FractionalIdeal.mem_one_iff]

variable {S T : HSp D}

theorem isSBHalf_comp₂ {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ') {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ' Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΨ
  refine ⟨fun t ht => (GlobalTheory.SchrMove.isHalf_actO_iff g h t).1 (h1 _ ht), k, hk, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · beta_reduce
    rw [GlobalTheory.SchrMove.actO_add, GlobalTheory.SchrMove.actO_nsmul]
    exact h2 _ ((hΛ u).1 hu) (GlobalTheory.SplitHecke.isHalf_actO g h hu') _
  · rw [hΛ, GlobalTheory.SchrMove.actO_nsmul]
    exact h3 _ ht

theorem halfInd_comp₂ {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ') (t : WO S T) : halfInd e Λ' (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos ht, if_pos ⟨(hΛ t).1 ht.1, GlobalTheory.SplitHecke.isHalf_actO g h ht.2⟩]
  · rw [if_neg ht, if_neg fun h' => ht ⟨(hΛ t).2 h'.1, (GlobalTheory.SchrMove.isHalf_actO_iff g h t).1 h'.2⟩]

theorem isPlaceModel_move₂ {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D}
    {Λ Λ' : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ')
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm)
    (hth : ∀ Ψ, IsSBHalf a Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ' 1 (om (g, h) f₀)
      (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h)) := by
  have ev : ∀ Ψ : WO S T → ℂ, (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h)) Ψ =
      om (g, h) (Tm fun t => Ψ (actO S T g h t)) := fun _ => rfl
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
  · have s := isSBHalf_comp₂ hΛ hΨ
    have e1 := hTm.trans _ s _ (GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ hx)
    have e2 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ x) _ (hth _ s)
    rw [GlobalTheory.AdelicLatMove.actO_actO_inv] at e2
    rw [ev, ev, ← e2, ← e1]
    simp only [GlobalTheory.SchrMove.actO_add, GlobalTheory.AdelicLatMove.actO_actO_inv]
  · have s := isSBHalf_comp₂ hΛ hΨ
    have e1 := hTm.modul _ s _ (GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ hy)
    have e2 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ y) _ (hth _ s)
    rw [GlobalTheory.AdelicLatMove.actO_actO_inv] at e2
    have e3 : ∀ t, symplO S T (actO S T g h t) y = symplO S T t (actO S T g⁻¹ h⁻¹ y) := fun t => by
      rw [← GlobalTheory.SplitHecke.symplO_actO S T g h t, GlobalTheory.AdelicLatMove.actO_actO_inv]
    rw [ev, ev, ← e2, ← e1]
    simp only [e3]
  · have v := hTm.vac
    rw [one_smul] at v
    have e1 : (fun t => halfInd a Λ' (actO S T g h t)) = halfInd a Λ := funext (halfInd_comp₂ hΛ)
    rw [one_smul, ev, e1, v]

end GlobalTheory.SplitMove

namespace GlobalTheory.SplitMove

theorem isThetaAt_move : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ f₀ Φ f, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ Φ f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ N N', Moves S hS g N → Moves T hT h N' → IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) (fun x => Φ (actO S T g⁻¹ h⁻¹ x)) ∧ IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) 1 (om (g, h) f₀) (fun x => Φ (actO S T g⁻¹ h⁻¹ x)) (om (g, h) f) := by
  intro D ψ θ S T a b hS hT δ sc hstd μ om hW e SS hSS f₀ Φ f hf₀ _hvac hΦ hf g _hg h _hh N N' hN hN'
  subst hS
  subst hT
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hSS
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hSS
  have sdS0 := selfDual_int S hstd.gS
  have sdT0 := selfDual_int T hstd.gT
  have sdS1 := selfDual_move S hstd.gS g N hN
  have sdT1 := selfDual_move T hstd.gT h N' hN'
  obtain ⟨fS, bS⟩ := hat_move S g N hN
  obtain ⟨fT, bT⟩ := hat_move T h N' hN'
  have e0 : stdHom S T = latO S T (intSub D S.rank : Set (Fin S.rank → D.host.E))
      (intSub D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True := rfl
  have e1 : latO S T (latFr S rfl N) (latFr T rfl N') (fun _ => True) =
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := rfl
  rw [e1]
  rw [e0] at hΦ hf
  have key : ∀ u, u ∈ latO S T (intSub D S.rank : Set (Fin S.rank → D.host.E))
      (intSub D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T g h u ∈ latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
    intro u
    refine ⟨GlobalTheory.MovedLat.actO_mem S T g h _ _ _ _ fS fT u, fun hu => ?_⟩
    have := GlobalTheory.MovedLat.actO_mem S T g⁻¹ h⁻¹ _ _ _ _ bS bT _ hu
    rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this
  have key' : ∀ u, u ∈ latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T g⁻¹ h⁻¹ u ∈ latO S T (intSub D S.rank : Set (Fin S.rank → D.host.E))
      (intSub D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True := by
    intro u
    refine ⟨GlobalTheory.MovedLat.actO_mem S T g⁻¹ h⁻¹ _ _ _ _ bS bT u, fun hu => ?_⟩
    have := GlobalTheory.MovedLat.actO_mem S T g h _ _ _ _ fS fT _ hu
    rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hstd.std S T _ _ sdS0 sdT0 e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨isSBHalf_comp₂ key' hΦ, ⟨_, isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hstd.std S T _ _ sdS1 sdT1 e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := isPlaceModel_move₂ hW key' hT' th1
  have ev : om (g⁻¹, h⁻¹) (om (g, h) f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (g⁻¹, h⁻¹) (T' fun t => Φ (actO S T g⁻¹ h⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

end GlobalTheory.SplitMove
