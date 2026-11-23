import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharactersStatement

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts GlobalTheory.AdTh
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh

theorem unr_of {D : D7} {χ : (AE D)ˣ →* Circle} (h : UnramEverywhere D χ) {v ε} (hε : IsPlaceIdem D v ε) : UnramAt ε χ := by
  intro x hx h1 h2
  refine h x ?_ h1 h2
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem isPair_pow (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (V W : HSp D) (h1 : V.gram = 1) (h2 : Even V.rank) (h3 : V.SigOK) (h4 : W.SigOK) (η) (hη : IsEtaTilde D η) :
    ∃ om, IsPair ψ θ V W (η ^ V.rank) (η ^ W.rank) om := by
  have hH : ∀ n : ℕ, IsHeckeChar D (η ^ n) := fun n =>
    ⟨by
      have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by funext x; simp
      rw [this]; exact hη.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩
  have hR : ∀ n : ℕ, ResEta D (η ^ n) n := fun n =>
    ⟨hη.2.2.1.1, fun e he a => by rw [MonoidHom.pow_apply, hη.2.2.1.2 e he a, pow_one]⟩
  have hE : ∀ (n : ℕ) τ, HasInfExp D (η ^ n) τ ((n : ℚ) / 2) := fun n τ => by
    obtain ⟨m, hm, ha, hb⟩ := hη.2.2.2 τ
    have hm1 : m = 1 := by
      have : (m : ℚ) = 1 := by rw [hm]; norm_num
      exact_mod_cast this
    subst hm1
    refine ⟨n, by push_cast; ring, ha, fun θ' hθ' x hx hx' => ?_⟩
    rw [MonoidHom.pow_apply, Circle.coe_pow, hb θ' hθ' x hx hx', zpow_one, zpow_natCast]
  have hU : ∀ n : ℕ, UnramEverywhere D (η ^ n) := fun n x a b c => by
    rw [MonoidHom.pow_apply, hη.2.1 x a b c, one_pow]
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hψ V W _ _ ⟨η, hη⟩ (hH _) (hH _) (hR _) (hR _)
  refine ⟨om, hom, hθ, h1, h2, h3, h4, fun τ => ?_, fun τ => ⟨0, by simpa using hE W.rank τ⟩,
    fun v ε h => ⟨unr_of (hU _) h.1, unr_of (hU _) h.1⟩, ⟨η, hη⟩⟩
  obtain ⟨a, ha⟩ := h2
  refine ⟨a, ?_⟩
  have := hE V.rank τ
  rwa [show ((V.rank : ℚ) / 2) = ((a : ℤ) : ℚ) by rw [ha]; push_cast; ring] at this

theorem isPair_rec (D : D7) (i : Fin D.R.m) (hV : VStd D i) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (η) (hη : IsEtaTilde D η) :
    0 < (Vc D i).rank ∧ 0 < (Wc D i).rank ∧ ∃ θ χV χW om, IsPair ψ θ (Vc D i) (Wc D i) χV χW om := by
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  obtain ⟨θ, hθ⟩ := hψ.2.1
  refine ⟨hr.trans_le (r_le_V i), hr.trans_le (r_le_rank_Wc i), θ, _, _,
    isPair_pow D ψ hψ θ hθ _ _ hV.1 ?_ (D.sp.V_sig _) (D.sp.W_sig _) η hη⟩
  rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2]
  exact (kapDom D).2

theorem hatC_phiHat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (φ : (Fin n → LevQc Dw l) → c.F) (hf : Finite (Fin n → LevQc Dw l)) (q : Fin n → LevQ Dw l) :
    hatC l (fun x => (φ x : ℂ)) q = ((phiHat c φ q : c.F) : ℂ) := by
  have hz : ((zetaM c : c.F) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
    have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by rintro rfl; simp at hk; exact hM' hk : k ≠ 0)
    simp only [zetaM, SubmonoidClass.coe_pow, zeta]
    rw [← Complex.exp_nat_mul, hk, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)]
    congr 1; push_cast; field_simp
  have := Fintype.ofFinite (Fin n → LevQc Dw l)
  unfold hatC phiHat
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← hz]
  show _ = c.F.val _
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀]
  rfl

theorem markAd_one {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (W : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) : MarkAd l W rfl ι 1 ι := by
  intro a _
  refine ⟨0, zero_mem _, ?_⟩
  rw [map_one, nsmul_zero, Units.val_one, Matrix.one_mulVec]
  exact sub_self _

end GlobalTheory.AdTh
