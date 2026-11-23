import Development.WeilBound.ThetaLifts.SmallCones.FcCols
import Development.WeilBound.ThetaLifts.SmallCones.UnfMain
import Development.WeilBound.ThetaLifts.SmallCones.StabDec
import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr Unf
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def fixQ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {δ | δ ∈ ratU σ J ∧ mat δ *ᵥ incV F x = incV F x}
  one_mem' := ⟨Subgroup.one_mem _, Matrix.one_mulVec _⟩
  mul_mem' := fun ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by rw [mat_mul, ← Matrix.mulVec_mulVec, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by conv_lhs => rw [← ha.2, mat_cancel]⟩

theorem exists_iso {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} (hg : g ∈ ratU σ J) {x : Fin n → E} (h0 : x ≠ 0)
    (hx : form σ J x x = 0) : ∃ z : Fin n → E, z ≠ 0 ∧ form σ J z z = 0 ∧ incV F z = mat g *ᵥ incV F x := by
  obtain ⟨M, hM⟩ := mem_ratU.1 hg
  have e : incV F (M *ᵥ x) = mat g *ᵥ incV F x := by
    rw [hM]
    exact funext fun i => RingHom.map_mulVec (inclR (F := F) (AF F)) M x i
  have hU : Mᵀ * J * M.map σ = J := by
    apply Matrix.map_injective (inclR_inj (F := F))
    have := g.2
    change (mat g)ᵀ * _ * (mat g).map _ = _ at this
    rw [hM] at this
    simp only [Matrix.map_mul]
    exact this
  refine ⟨M *ᵥ x, fun h => h0 (funext fun i => inclR_inj (F := F) ?_), ?_, e⟩
  · have := mat_cancel g (incV F x)
    rw [← e, h, show incV F (0 : Fin n → E) = 0 from funext fun _ => map_zero _, Matrix.mulVec_zero] at this
    exact (congrFun this i).symm.trans (map_zero _).symm
  · have e2 : (fun i => σ ((M *ᵥ x) i)) = M.map σ *ᵥ fun i => σ (x i) := funext fun i => RingHom.map_mulVec (σ : E →+* E) M x i
    rw [← hx, form, form, e2]
    conv_rhs => rw [← hU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

theorem unfold_of : Unfold := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s hB hX hH K μK μ ν D ν₁ D₁ lev hK _ _ _ hD _ hD₁ hlev
  have hY : X.IsHerm σ B r s ∨ X.IsSkew σ B r s := Or.inl hX
  obtain ⟨ε, A', hfr⟩ := isFr hB hY hH
  have hd : IsUnit X₁.J.det := hfr.isUnit_det (det_ne hY).isUnit
  have hJ : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX.herm]
  have hJ₁ : ∀ i j, σ (X₁.J j i) = (((1 : ℤˣ) : ℤ) : E) * X₁.J i j := fun i j => by
    have e : ∀ i j, X₁.J i j = form σ X.J (fun k => H.ι k i) (fun k => H.ι k j) := fun i j => by
      rw [← hH.gram, Matrix.mul_assoc]; rfl
    rw [e, e, form_eps (PositivityTheory.ThKG.Tow.Levi.sig_sig hB.cm) hJ]
  obtain ⟨_, _, _, _, _, -⟩ := PositivityTheory.ThKF.unimodLC hB.cm hJ (det_ne hY)
  obtain ⟨_, _, _, _, _, -⟩ := PositivityTheory.ThKF.unimodLC hB.cm hJ₁ hd.ne_zero
  obtain ⟨-, _, _, _, _, _, -⟩ := ideleTop F E
  haveI := PositivityTheory.ThKF.countable_ratU σ X.J
  haveI := PositivityTheory.ThKF.countable_ratU σ X₁.J
  haveI := PositivityTheory.ThKF.discrete_ratU hB.cm hJ (det_ne hY)
  obtain ⟨s1, s2, s3⟩ := stabDec_of F E σ B n n₁ X X₁ H j₀ j₁ r s hB hY hH
  obtain ⟨N, _, _, _, _, μN, _, _, nn, ι, mm, χ, hP, c1, c2, c3, -, C, hC, hcov⟩ := parEx hB hY hH
  have l1 : ∀ g, IsLevi H 1 g (ι g) := fun g => by simpa using c3 1 g
  have l2 : ∀ g ∈ ratU σ X₁.J, ι g ∈ ratU σ X.J := fun g hg => s2 1 g hg _ (by rw [map_one]; exact l1 g)
  have el : ∀ t g, lev (t, g) = ι g * mm t := fun t g => levi_uniq hfr (hlev t g) (c3 t g)
  have eχ : ∀ t, (absE F E t : ℝ) ^ (1 - (n : ℝ)) = χ t := fun t => by
    have h1 : (χ t : ℝ) * (absE F E t : ℝ) ^ (n₁ + 1) = 1 := by exact_mod_cast c1 t
    rw [eq_inv_of_mul_eq_one_left h1, ← Real.rpow_natCast, ← Real.rpow_neg (NNReal.coe_nonneg _), hH.rank]
    congr 1
    push_cast
    ring
  obtain ⟨κ, hκ, hmain⟩ := unfold_abs ν ν₁ μ hP hK.1 μK (Γ := ratU σ X.J) (Q := fixQ X.J H.x)
    (ΓN := ratU σ X.J ⊓ unip σ X H) (Γ₁ := ratU σ X₁.J) (fun g => by
      obtain ⟨p, k, l, hk, hp, rfl⟩ := hK.2 g
      obtain ⟨u, hu, g₁, m, hm, rfl, -⟩ := s1 p l hp
      obtain ⟨q, rfl⟩ := (c2 u).1 hu
      exact ⟨q, g₁, l, k, hk, by rw [levi_uniq hfr hm (c3 l g₁), ← mul_assoc (nn q)]⟩)
    (fun _ h => h.1) (fun δ h => ⟨h.1, (mem_unip.1 h.2).1⟩) (fun δ h => (c2 δ).1 h.2)
    (fun γ h => ⟨l2 γ h, (l1 γ).1.trans (one_smul _ _)⟩) (fun q hq => by
      obtain ⟨u, hu, g₁, m, hm, rfl, hr⟩ := s1 q 1 (hq.2.trans (one_smul _ _).symm)
      obtain rfl := levi_uniq hfr hm (l1 g₁)
      have key : ∀ z z' : ratU σ X₁.J × (ratU σ X.J ⊓ unip σ X H : Subgroup _), ι z.1 * z.2 = ι z'.1 * z'.2 → z = z' :=
        fun z z' e => by
          obtain ⟨p, hp⟩ := (c2 _).1 z.2.2.2
          obtain ⟨p', hp'⟩ := (c2 _).1 z'.2.2.2
          obtain ⟨L, -, hL⟩ := hP.h2 z.1
          obtain ⟨L', -, hL'⟩ := hP.h2 z'.1
          have e1 : z.1 = z'.1 := Subtype.ext (congrArg (fun w => w.2.1)
            (hP.emb.injective (a₁ := (L p, z.1.1, 1)) (a₂ := (L' p', z'.1.1, 1)) (by
              simp only [map_one, mul_one, ← hL, ← hL', ← hp, ← hp', e])))
          rw [e1] at e
          exact Prod.ext e1 (Subtype.ext (mul_left_cancel e))
      refine ⟨(⟨g₁, hr hq.1⟩, ⟨(ι g₁)⁻¹ * u * ι g₁, ?_, levi_conj hm hu⟩), by simp only; group, fun z hz => key _ _ ?_⟩
      · rw [mul_assoc]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (l2 _ (hr hq.1))) hq.1
      · rw [← hz]; simp only; group)
    hC (fun p => by
      obtain ⟨q, h1, h2⟩ := hcov p
      exact ⟨nn q, ⟨h1, (c2 _).2 ⟨q, rfl⟩⟩, h2⟩) hD₁ hD
  refine ⟨κ, hκ, fun γ hγ f hf i1 i2 hfin => ?_⟩
  simp only [el, eχ, ENNReal.ofReal_coe_nnreal] at hfin ⊢
  refine hmain _ γ (fun x => (hγ x).1) (fun g hg => ?_) f hf (fun p => i1 _ ((c2 _).2 ⟨p, rfl⟩)) (fun q hq => i2 q hq.1 hq.2) hfin
  have hx0 : H.x ≠ 0 := fun h => by
    have := hH.xy
    rw [h, form, zero_dotProduct] at this
    exact zero_ne_one this
  have k : ∀ x : IsoV σ X, g * (γ x)⁻¹ ∈ fixQ X.J H.x ↔ incV F x.1 = mat g⁻¹ *ᵥ incV F H.x := fun x => by
    have e : mat (g * (γ x)⁻¹) *ᵥ incV F H.x = mat g *ᵥ incV F x.1 := by
      rw [mat_mul, ← Matrix.mulVec_mulVec, ← (hγ x).2, mat_cancel]
    refine ⟨fun h => by rw [← h.2, e, mat_cancel], fun h => ⟨Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (hγ x).1), ?_⟩⟩
    rw [e, h, mat_cancel']
  obtain ⟨z, z0, z1, z2⟩ := exists_iso (Subgroup.inv_mem _ hg) hx0 hH.xx
  exact ⟨⟨z, z0, z1⟩, (k _).2 z2, fun x hx => Subtype.ext (funext fun i => inclR_inj (F := F)
    (congrFun (((k x).1 hx).trans z2.symm) i))⟩

end PositivityTheory.ThKCT

end
