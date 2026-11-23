import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrouStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.DivP

open WithConv

variable {p : ℕ} {k : Type} [Field k]

theorem conv_eq_one_of_succ {G H : PDivGroup p k} (f : G ⟶ H) (n : ℕ) (h : f.conv (n + 1) = 1) :
    f.conv n = 1 := by
  have h1 : ∀ b, f.app (n + 1) b = algebraMap k _ (counit b) := fun b => by
    have := DFunLike.congr_fun (congrArg ofConv h) b
    simpa using this
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  change f.app n (H.res n b) = algebraMap k _ (counit (H.res n b))
  rw [← res_app, h1, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

theorem conv_eq_one_of_le {G H : PDivGroup p k} (f : G ⟶ H) {m n : ℕ} (hmn : m ≤ n)
    (h : f.conv n = 1) : f.conv m = 1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (conv_eq_one_of_succ f n h)

theorem app_kill {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) (n : ℕ) :
    ∀ {E : Type} [CommRing E] [Algebra k E] (x : G.A (n + 1) →ₐ[k] E), toConv x ^ p = 1 →
      ∀ c, x (f.app (n + 1) c) = algebraMap k E (counit c) := by
  induction n with
  | zero =>
    intro E _ _ x _ c
    have h1 : f.app 1 c = algebraMap k _ (counit c) := by
      have := DFunLike.congr_fun (congrArg ofConv hf) c
      simpa using this
    rw [h1, AlgHom.commutes]
  | succ n ih =>
    intro E _ _ x hx c
    have hx' : toConv x ^ p ^ (n + 1) = 1 := by
      rw [pow_succ', pow_mul, hx, one_pow]
    obtain ⟨y, hy⟩ := (G.exists_comp_res_iff (n + 1) x).2 hx'
    have hy' : toConv y ^ p = 1 := by
      have e : pointsMap E (G.res (n + 1)) (toConv y ^ p) = 1 := by
        rw [map_pow]
        change (toConv (y.comp (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)))) ^ p = 1
        rw [hy, hx]
      apply ofConv_injective
      refine AlgHom.ext fun a => ?_
      obtain ⟨b, rfl⟩ := G.res_surjective (n + 1) a
      have e2 := DFunLike.congr_fun (congrArg ofConv e) b
      rw [ptsMap_ofConv, AlgHom.comp_apply] at e2
      refine e2.trans ?_
      show algebraMap k E (counit b) = algebraMap k E (counit (G.res (n + 1) b))
      rw [CoalgHomClass.counit_comp_apply]
    rw [← hy, AlgHom.comp_apply]
    change y (G.res (n + 1) (f.app (n + 2) c)) = _
    rw [res_app, ih y hy', CoalgHomClass.counit_comp_apply]

theorem exists_factor [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1)
    (n : ℕ) : ∃ g : H.A (n + 1) →ₐc[k] G.A n, ∀ b, G.mulP n (g b) = f.app (n + 1) b := by
  obtain ⟨r, hrs, hrk⟩ := G.exists_res_le (m := 1) (n := n + 1) (by omega)
  rw [pow_one] at hrk
  obtain ⟨B, _, _, _, _, j, hji, hjk, hjr⟩ := GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup k (G.A (n + 1)) (G.A 1) r hrs
  have hP : kerIdeal (G.mulP n) = RingHom.ker r := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective n), mulP_comp_res, hrk]
  have h1 : ∀ a, G.mulP n a ∈ Set.range j := hjr (G.A n) (G.mulP n) hP.le
  have hmk : toConv (Ideal.Quotient.mkₐ k (torsionIdeal k (G.A (n + 1)) p)) ^ p = 1 :=
    (torsionIdeal_le_ker_iff p _).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h2 : ∀ b, f.app (n + 1) b ∈ Set.range j := by
    refine hjr (H.A (n + 1)) (f.app (n + 1)) ?_
    rw [hrk]
    intro a ha
    have := (kerIdeal_le_ker_iff (f.app (n + 1)) (Ideal.Quotient.mkₐ k _)).2
      (fun c => app_kill f hf n _ hmk c) ha
    rw [RingHom.mem_ker] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  let jl := (j : B →ₐ[k] G.A (n + 1)).toLinearMap
  let ml := (G.mulP n : G.A n →ₐ[k] G.A (n + 1)).toLinearMap
  have hle : LinearMap.range ml ≤ LinearMap.range jl := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := h1 a
    exact ⟨b, hb⟩
  have e1 := finrank_eq_ker_mul_range k (G.A (n + 1)) (G.A n) (G.mulP n)
  have e2 := finrank_eq_ker_mul_range k (G.A (n + 1)) B j
  rw [hP] at e1
  rw [hjk] at e2
  have hpos : 0 < Module.finrank k (G.A (n + 1) ⧸ RingHom.ker r) := by
    apply Nat.pos_of_ne_zero
    intro h0
    have : Nontrivial (G.A (n + 1)) := (counitAlgHom k (G.A (n + 1))).domain_nontrivial
    have h3 := Module.finrank_pos (R := k) (M := G.A (n + 1))
    rw [e1, h0, zero_mul] at h3
    exact lt_irrefl _ h3
  have heq : LinearMap.range ml = LinearMap.range jl :=
    Submodule.eq_of_le_of_finrank_eq hle (Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans e2))
  have h3 : ∀ b, f.app (n + 1) b ∈ Set.range (G.mulP n) := by
    intro b
    obtain ⟨c, hc⟩ := h2 b
    have : f.app (n + 1) b ∈ LinearMap.range ml := by
      rw [heq]
      exact ⟨c, hc⟩
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective ml
    (LinearMap.ker_eq_bot.2 (Test.mulP_injective G n))
  exact GlobalTheory.bialgHom_factor_through_split k (G.A (n + 1)) (G.A n) (H.A (n + 1)) (G.mulP n) ρ
    (f.app (n + 1)) (fun a => LinearMap.congr_fun hρ a) h3

theorem exists_eq_p_smul [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  choose g' hg' using exists_factor f hf
  have hker : ∀ n, RingHom.ker (H.res n) ≤ RingHom.ker (g' n) := by
    intro n
    rw [H.ker_res]
    refine (kerIdeal_le_ker_iff _ (g' n : H.A (n + 1) →ₐ[k] G.A n)).2 fun c => ?_
    change g' n (mulBy k _ (p ^ n) c) = _
    rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]
  let gapp : ∀ n, H.A n →ₐc[k] G.A n := fun n =>
    liftSurj (H.res n) (H.res_surjective n) (g' n) (hker n)
  have hg : ∀ n b, gapp n (H.res n b) = g' n b := fun n b => liftSurj_apply ..
  have hcomm : ∀ n, (G.res n).comp (gapp (n + 1)) = (gapp n).comp (H.res n) := by
    intro n
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective (n + 1) a
    apply Test.mulP_injective G n
    change G.mulP n (G.res n (gapp (n + 1) (H.res (n + 1) b))) =
      G.mulP n (gapp n (H.res n (H.res (n + 1) b)))
    rw [hg, hg, mulP_res, hg' n, ← res_app, ← hg' (n + 1) b, res_mulP]
  refine ⟨⟨gapp, hcomm⟩, hom_ext_conv fun n => ?_⟩
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self n _)]
  have hfa : f.app n = (mulBy k (G.A n) p).comp (gapp n) := by
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective n a
    rw [← res_app, ← hg' n b, res_mulP, BialgHom.comp_apply, hg]
  change toConv (f.app n) = toConv (gapp n) ^ p
  rw [hfa, mulBy_comp, toConv_ofConv]

theorem conv_eq_one_of_p_smul [Fact p.Prime] {G H : PDivGroup p k} (g : G ⟶ H) (m : ℕ)
    (h : ((p : ℤ_[p]) • g).conv (m + 1) = 1) : g.conv m = 1 := by
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self _ _)] at h
  have h' : ∀ b, mulBy k (G.A (m + 1)) p (g.app (m + 1) b) = algebraMap k _ (counit b) := by
    intro b
    have e := DFunLike.congr_fun (congrArg ofConv h) b
    have e2 := DFunLike.congr_fun (mulBy_comp (g.app (m + 1)) p) b
    rw [BialgHom.comp_apply] at e2
    rw [e2]
    simpa using e
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective m a
  apply Test.mulP_injective G m
  change G.mulP m (g.app m (H.res m b)) = G.mulP m (algebraMap k _ (counit (H.res m b)))
  rw [← res_app, mulP_res, h', CoalgHomClass.counit_comp_apply]
  exact (AlgHomClass.commutes (G.mulP m) _).symm

theorem exists_eq_pow_smul [Fact p.Prime] {G H : PDivGroup p k} (m : ℕ) :
    ∀ f : G ⟶ H, f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  induction m with
  | zero => exact fun f _ => ⟨f, by rw [pow_zero, one_smul]⟩
  | succ m ih =>
    intro f hf
    obtain ⟨g, rfl⟩ := exists_eq_p_smul f (conv_eq_one_of_le f (by omega) hf)
    obtain ⟨g2, rfl⟩ := ih g (conv_eq_one_of_p_smul g m hf)
    exact ⟨g2, by rw [smul_smul, ← pow_succ']⟩

theorem divisible_of_conv_eq_one : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g :=
  fun _ _ _ _ _ _ _ m f hf => exists_eq_pow_smul m f hf

end GlobalTheory.PDivGroup.DivP
