import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankInverseBounds
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankLinkProof
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf

noncomputable section

namespace Formalism.MainNotions.N.Ln34.RankBounds

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct
open scoped Classical

section Flag

variable {O V : Type*} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]

open Formalism.MainNotions.N.Ln34.RankInverseBounds in

theorem rank_inv_le_lt (γ : V →ₗ[O] V) (K' : Submodule O V) (hK : ∀ x ∈ K', γ x ∈ K') :
    ∀ (N : ℕ) (F : ℕ → Submodule O V) (c : ℕ → O), (∀ k < N, F (k + 1) ≤ F k) →
      (∀ k < N, ∀ x ∈ F k, γ x - c k • x ∈ F (k + 1)) → F N ≤ K' →
      Module.rank O (InvQ γ K' (F 0)) ≤
        ∑ k ∈ Finset.range N, (if c k = 1 then Module.rank O (Gr (F k) (F (k + 1))) else 0) := by
  intro N
  induction N with
  | zero =>
    intro F c _ _ hN
    simp only [Finset.range_zero, Finset.sum_empty, nonpos_iff_eq_zero]
    refine rank_eq_zero_iff.mpr fun q => ⟨1, one_ne_zero, ?_⟩
    induction q using Submodule.Quotient.induction_on with | H x => ?_
    rw [one_smul, Submodule.Quotient.mk_eq_zero]
    exact hN (Submodule.mem_inf.mp x.2).1
  | succ N ih =>
    intro F c hm hγ hN
    have h1 := step γ K' hK (F 0) (F 1) (c 0) (hm 0 (Nat.succ_pos _)) (hγ 0 (Nat.succ_pos _))
    have h2 := ih (fun k => F (k + 1)) (fun k => c (k + 1)) (fun k hk => hm (k + 1) (by omega))
      (fun k hk => hγ (k + 1) (by omega)) hN
    rw [Finset.sum_range_succ']
    exact h1.trans (add_le_add h2 le_rfl)

end Flag

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)

def smulE (e : W.EE) : LA W T π' c →ₗ[O] LA W T π' c :=
  TensorProduct.map (LinearMap.mulLeft O e) LinearMap.id

variable {W T π' c}

theorem smulE_tmul (e x : W.EE) (y : LcQ W T π' c) : smulE W T π' c e (x ⊗ₜ y) = (e * x) ⊗ₜ y := by
  simp [smulE, TensorProduct.map_tmul]

theorem smulLA_eq (a : LetA O n) : smulLA W T π' c a = smulE W T π' c (algebraMap (LetA O n) W.EE a) := rfl

theorem smulE_smulE (e e' : W.EE) (x : LA W T π' c) :
    smulE W T π' c e (smulE W T π' c e' x) = smulE W T π' c (e * e') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [smulE_tmul, mul_assoc]
  | add x y hx hy => simp [map_add, hx, hy]

theorem smulE_one (x : LA W T π' c) : smulE W T π' c 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [smulE_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem smulE_inj {e : W.EE} (he : IsUnit e) : Function.Injective (smulE W T π' c e) := by
  obtain ⟨u, rfl⟩ := he
  intro x y h
  have := congrArg (smulE W T π' c (↑u⁻¹ : W.EE)) h
  rwa [smulE_smulE, smulE_smulE, Units.inv_mul, smulE_one, smulE_one] at this

theorem γLA_tmul (x : W.EE) (y : LcQ W T π' c) : γLA W T π' c (x ⊗ₜ y) = (W.γE W.gamK x) ⊗ₜ y := by
  simp [γLA, TensorProduct.map_tmul]

theorem γLA_smulE (e : W.EE) (x : LA W T π' c) :
    γLA W T π' c (smulE W T π' c e x) = smulE W T π' c (W.γE W.gamK e) (γLA W T π' c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [smulE_tmul, γLA_tmul, map_mul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem toLA_tmul (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := by
  simp [toLA, TensorProduct.map_tmul]

theorem γE_alg (g : W.Gam) (a : LetA O n) :
    W.γE g (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE (W.γA g a) := W.γE_ext g a

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i : LetA O n) = letE i := by
  funext j
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, letE]
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

variable (S : Submodule O (LcQ W T π' c))

theorem R_smul {b : LetA O n} (hb : b ∈ W.AΔ) {r : LA W T π' c}
    (hr : r ∈ LinearMap.range (toLA W T π' c S)) : smulLA W T π' c b r ∈ LinearMap.range (toLA W T π' c S) := by
  obtain ⟨t, rfl⟩ := hr
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a s =>
    refine ⟨(⟨b, hb⟩ * a) ⊗ₜ s, ?_⟩
    rw [toLA_tmul, toLA_tmul, smulLA_eq, smulE_tmul, ← map_mul]
    congr 2
    simp only [Subalgebra.coe_mul]
    ring
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

theorem R_smul_letE (p : LetA O n) {r : LA W T π' c} (hr : r ∈ LinearMap.range (toLA W T π' c S)) :
    smulLA W T π' c p r = smulLA W T π' c ((letE c : LetA O n) * p) r := by
  obtain ⟨t, rfl⟩ := hr
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a s =>
    rw [toLA_tmul, smulLA_eq, smulLA_eq, smulE_tmul, smulE_tmul, ← map_mul, ← map_mul]
    congr 2
    have he : (letE c : LetA O n) * letE c = letE c := by
      funext j; simp only [letE, Pi.mul_apply, Pi.single_apply]; split_ifs <;> simp
    calc p * ((letE c : LetA O n) * (a : LetA O n)) = p * ((letE c * letE c) * (a : LetA O n)) := by rw [he]
      _ = _ := by ring
  | add x y hx hy => simp only [map_add, hx, hy]

def Fl (Eπ : LetA O n) (h' : ℕ) (f : ℕ → LetA O n) (k : ℕ) : Submodule O (LA W T π' c) :=
  ((LinearMap.range (toLA W T π' c S)).map (smulLA W T π' c (∏ j ∈ Finset.range k, f j))).comap
    (smulLA W T π' c (Eπ ^ h'))

theorem smulLA_one : smulLA W T π' c 1 = LinearMap.id :=
  LinearMap.ext fun x => by rw [smulLA_eq, map_one, LinearMap.id_apply, smulE_one]

theorem smulLA_mul (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c (a * b) x = smulLA W T π' c a (smulLA W T π' c b x) := by
  rw [smulLA_eq, smulLA_eq, smulLA_eq, smulE_smulE, map_mul]

theorem Fl_zero (Eπ : LetA O n) (h' : ℕ) (f : ℕ → LetA O n) :
    Fl S Eπ h' f 0 = LamLA W T π' Eπ h' c S := by
  simp only [Fl, Finset.range_zero, Finset.prod_empty, smulLA_one, Submodule.map_id, LamLA]

theorem Fl_mono (Eπ : LetA O n) (h' : ℕ) (f : ℕ → LetA O n) (k : ℕ) (hf : f k ∈ W.AΔ) :
    Fl S Eπ h' f (k + 1) ≤ Fl S Eπ h' f k := by
  intro x hx
  obtain ⟨r, hr, hrx⟩ := hx
  refine ⟨smulLA W T π' c (f k) r, R_smul S hf hr, ?_⟩
  rw [← hrx, Finset.prod_range_succ, smulLA_mul]

theorem Fl_gamma (Eπ : LetA O n) (h' : ℕ) (f : ℕ → LetA O n) (cc : ℕ → O) (ν : LetA O n)
    (hν : ν * W.γA W.gamK (Eπ ^ h') = Eπ ^ h') (k : ℕ)
    (hγc : ∀ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      (letE c : LetA O n) * (ν * W.γA W.gamK ((∏ j ∈ Finset.range k, f j) * a) -
          algebraMap O (LetA O n) (cc k) * ((∏ j ∈ Finset.range k, f j) * a)) =
        (letE c : LetA O n) * ((∏ j ∈ Finset.range (k + 1), f j) * b)) :
    ∀ x ∈ Fl S Eπ h' f k, γLA W T π' c x - cc k • x ∈ Fl S Eπ h' f (k + 1) := by
  intro x hx
  obtain ⟨r, hr, hrx⟩ := hx
  set Pk := ∏ j ∈ Finset.range k, f j with hPk
  have e1 : smulLA W T π' c (Eπ ^ h') (γLA W T π' c x) =
      smulLA W T π' c ν (smulLA W T π' c (W.γA W.gamK Pk) (γLA W T π' c r)) := by
    calc smulLA W T π' c (Eπ ^ h') (γLA W T π' c x)
        = smulLA W T π' c (ν * W.γA W.gamK (Eπ ^ h')) (γLA W T π' c x) := by rw [hν]
      _ = smulLA W T π' c ν (smulLA W T π' c (W.γA W.gamK (Eπ ^ h')) (γLA W T π' c x)) :=
          smulLA_mul _ _ _
      _ = smulLA W T π' c ν (γLA W T π' c (smulLA W T π' c (Eπ ^ h') x)) := by
          rw [smulLA_eq (W.γA W.gamK (Eπ ^ h')), ← γE_alg, ← γLA_smulE, ← smulLA_eq]
      _ = smulLA W T π' c ν (γLA W T π' c (smulLA W T π' c Pk r)) := by rw [hrx]
      _ = _ := by rw [smulLA_eq Pk, γLA_smulE, γE_alg, ← smulLA_eq]
  show smulLA W T π' c (Eπ ^ h') (γLA W T π' c x - cc k • x) ∈
    (LinearMap.range (toLA W T π' c S)).map (smulLA W T π' c (∏ j ∈ Finset.range (k + 1), f j))
  rw [map_sub, map_smul, e1, ← hrx]
  clear e1 hrx
  obtain ⟨t, rfl⟩ := hr
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a s =>
    obtain ⟨b, hb, hbeq⟩ := hγc a a.2
    refine ⟨toLA W T π' c S (⟨b, hb⟩ ⊗ₜ s), ⟨_, rfl⟩, ?_⟩
    simp only [toLA_tmul, γLA_tmul, γE_alg, smulLA_eq, smulE_tmul, TensorProduct.smul_tmul',
      ← TensorProduct.sub_tmul]
    congr 1
    have h2 := congrArg (algebraMap (LetA O n) W.EE) hbeq
    simp only [map_mul, map_sub, γA_letE] at h2 ⊢
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
    linear_combination h2.symm
  | add x y hx hy =>
    have := add_mem hx hy
    convert this using 1
    simp only [map_add, smul_add]
    abel

theorem piNL_gamma (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (Eπ : LetA O n) (h' M : ℕ)
    (hML : ModelL W T Pt π' Eπ h' M c) {g : LetA O n} (hg : g ∈ W.AΔ) (hgπ : W.γA W.gamK π' = π' * g) :
    ∀ y ∈ piNL W T Pt π' Eπ h' c 1, γLA W T π' c y ∈ piNL W T Pt π' Eπ h' c 1 := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨smulLA W T π' c g (γLA W T π' c z), hML.2.2.1 g hg _ (hML.2.1 z hz), ?_⟩
  rw [pow_one, ← smulLA_mul, smulLA_eq π', γLA_smulE, γE_alg, hgπ, ← smulLA_eq]

theorem Fl_last (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (Eπ : LetA O n) (h' M : ℕ)
    (hML : ModelL W T Pt π' Eπ h' M c) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (N : ℕ) (f : ℕ → LetA O n)
    (hprod : (letE c : LetA O n) * ∏ k ∈ Finset.range N, f k = (letE c : LetA O n) * (π' * Eπ ^ (2 * h'))) :
    Fl S Eπ h' f N ≤ piNL W T Pt π' Eπ h' c 1 := by
  intro x hx
  obtain ⟨r, hr, hrx⟩ := hx
  have h1 : smulLA W T π' c (∏ k ∈ Finset.range N, f k) r =
      smulLA W T π' c (Eπ ^ h') (smulLA W T π' c (π' * Eπ ^ h') r) := by
    rw [R_smul_letE S _ hr, hprod, ← R_smul_letE S _ hr, ← smulLA_mul]
    congr 1
    rw [mul_comm 2 h', pow_mul]
    ring
  rw [h1] at hrx
  have hu : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow h'
  have hx' := smulE_inj (W := W) (T := T) (π' := π') (c := c) hu hrx
  rw [← hx']
  refine ⟨smulLA W T π' c (Eπ ^ h') r, hML.2.2.2.1 ⟨r, ?_, rfl⟩, ?_⟩
  · exact RankLink.toLA_range_le W T π' c S hr
  · rw [pow_one, ← smulLA_mul]

theorem Fl_gr_rank (Eπ : LetA O n) (h' : ℕ) (f : ℕ → LetA O n)
    (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (k : ℕ)
    (hdiv : ∀ a ∈ W.AΔ, ∃ (a₀ : O) (b : LetA O n), b ∈ W.AΔ ∧
      (letE c : LetA O n) * a = (letE c : LetA O n) * (algebraMap O (LetA O n) a₀ + f k * b)) :
    Module.rank O (Formalism.MainNotions.N.Ln34.RankInverseBounds.Gr (Fl S Eπ h' f k) (Fl S Eπ h' f (k + 1))) ≤
      Module.rank O S := by
  have hu : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow h'
  set Λi : W.EE := ↑(hu.unit⁻¹) with hΛi
  have hΛ : algebraMap (LetA O n) W.EE (Eπ ^ h') * Λi = 1 := by
    rw [hΛi]; exact hu.mul_val_inv
  set Pk := ∏ j ∈ Finset.range k, f j with hPk
  let e0 : ↥S →ₗ[O] LA W T π' c :=
    smulE W T π' c Λi ∘ₗ smulLA W T π' c Pk ∘ₗ toLA W T π' c S ∘ₗ TensorProduct.mk O ↥W.AΔ ↥S 1
  have he0s : ∀ s : ↥S, smulLA W T π' c (Eπ ^ h') (e0 s) =
      smulLA W T π' c Pk (toLA W T π' c S (1 ⊗ₜ s)) := by
    intro s
    simp only [e0, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply]
    rw [smulLA_eq (Eπ ^ h'), smulE_smulE, hΛ, smulE_one]
  have he0 : ∀ s : ↥S, e0 s ∈ Fl S Eπ h' f k := fun s =>
    ⟨toLA W T π' c S (1 ⊗ₜ s), ⟨_, rfl⟩, (he0s s).symm⟩
  let θ := ((Fl S Eπ h' f (k + 1)).comap (Fl S Eπ h' f k).subtype).mkQ ∘ₗ
    LinearMap.codRestrict (Fl S Eπ h' f k) e0 he0
  have key : ∀ r ∈ LinearMap.range (toLA W T π' c S), ∃ s : ↥S,
      r - toLA W T π' c S (1 ⊗ₜ s) ∈ (LinearMap.range (toLA W T π' c S)).map (smulLA W T π' c (f k)) := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a s =>
      obtain ⟨a₀, b, hb, hab⟩ := hdiv a a.2
      refine ⟨a₀ • s, toLA W T π' c S (⟨b, hb⟩ ⊗ₜ s), ⟨_, rfl⟩, ?_⟩
      rw [toLA_tmul, toLA_tmul, toLA_tmul, smulLA_eq, smulE_tmul, Submodule.coe_smul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
      congr 1
      have h2 := congrArg (algebraMap (LetA O n) W.EE) hab
      simp only [map_mul, map_add, Subalgebra.coe_one, mul_one] at h2 ⊢
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      linear_combination -h2
    | add x y hx hy =>
      obtain ⟨s₁, hs₁⟩ := hx
      obtain ⟨s₂, hs₂⟩ := hy
      refine ⟨s₁ + s₂, ?_⟩
      have := add_mem hs₁ hs₂
      convert this using 1
      simp only [map_add, TensorProduct.tmul_add]
      abel
  have hsurj : Function.Surjective θ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | H x => ?_
    obtain ⟨r, hr, hrx⟩ := x.2
    obtain ⟨s, r', hr', hs⟩ := key r hr
    refine ⟨s, ?_⟩
    simp only [θ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    show ((LinearMap.codRestrict (Fl S Eπ h' f k) e0 he0 s : LA W T π' c) - (x : LA W T π' c)) ∈
      Fl S Eπ h' f (k + 1)
    refine ⟨-r', (LinearMap.range (toLA W T π' c S)).neg_mem hr', ?_⟩
    simp only [LinearMap.codRestrict_apply, map_sub, he0s, ← hrx]
    rw [Finset.prod_range_succ, smulLA_mul, ← hPk, map_neg, hs, ← map_sub]
    congr 1
    abel
  exact LinearMap.rank_le_of_surjective θ hsurj

variable [IsDomain O]

theorem u2rank_local [IsNoetherianRing O] (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (Eπ : LetA O n) (h' M : ℕ)
    (hML : ModelL W T Pt π' Eπ h' M c) (hR : SecondPropositionRingInput W π' Eπ h' c)
    (hfin : Module.Finite O (LcQ W T π' c)) : SecondRankCount W T Pt π' Eπ h' c := by
  intro S
  obtain ⟨_, hEu, ⟨g, hgΔ, hgπ⟩, ν, _, hν, N, f, cc, hfΔ, hprod, hdiv, hγc, hcount⟩ := hR
  have hK := piNL_gamma Pt Eπ h' M hML hgΔ hgπ
  have hr := rank_inv_le_lt (γLA W T π' c) (piNL W T Pt π' Eπ h' c 1) hK N (Fl S Eπ h' f) cc
    (fun k _ => Fl_mono S Eπ h' f k (hfΔ k)) (fun k hk => Fl_gamma S Eπ h' f cc ν hν k (hγc k hk))
    (Fl_last S Pt Eπ h' M hML hEu N f hprod)
  rw [Fl_zero] at hr
  have hb : (∑ k ∈ Finset.range N, (if cc k = 1 then
      Module.rank O (Formalism.MainNotions.N.Ln34.RankInverseBounds.Gr (Fl S Eπ h' f k) (Fl S Eπ h' f (k + 1))) else 0)) ≤
      (((finrank K₀ K + 1 : ℕ) : Cardinal) * Module.rank O S) := by
    calc _ ≤ ∑ k ∈ Finset.range N, (if cc k = 1 then Module.rank O S else 0) := by
          refine Finset.sum_le_sum fun k hk => ?_
          split_ifs
          · exact Fl_gr_rank S Eπ h' f hEu k (hdiv k (Finset.mem_range.mp hk))
          · exact le_rfl
      _ = (((Finset.range N).filter fun k => cc k = 1).card : Cardinal) * Module.rank O S := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr
  have : IsNoetherian O (LcQ W T π' c) := inferInstance
  have : Module.Finite O ↥S := Module.Finite.of_injective S.subtype Subtype.val_injective
  have hle : Module.rank O (IIrest W T Pt π' Eπ h' c S) ≤ (((finrank K₀ K + 1) * finrank O ↥S : ℕ) : Cardinal) := by
    rw [Nat.cast_mul, Module.finrank_eq_rank]
    exact hr.trans hb
  unfold Module.finrank
  calc Cardinal.toNat (Module.rank O (IIrest W T Pt π' Eπ h' c S))
      ≤ Cardinal.toNat ((((finrank K₀ K + 1) * finrank O ↥S : ℕ) : Cardinal)) :=
        Cardinal.toNat_le_toNat hle (Cardinal.natCast_lt_aleph0)
    _ = _ := by rw [Cardinal.toNat_natCast]; rfl

omit [IsDomain O] in
theorem mem_letS (i : ZMod n) (x : W.DD T) : x ∈ letS W T i ↔ (letE i : LetA O n) • x = x := by
  simp [letS, LinearMap.mem_ker, sub_eq_zero]

omit [IsDomain O] in
theorem mem_DelS (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  simp [DelS, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

omit [IsDomain O] in

theorem lcq_finite_local (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0)
    (hexp : ∀ a ∈ W.AΔ, ∃ F : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (F i))
    (r : ℕ) (b : Fin r → W.DD T) (hb : ∀ j, b j ∈ W.NΔ T)
    (hspan : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j) :
    Module.Finite O (LcQ W T π' c) := by
  classical
  set e : LetA O n := letE (c - 1) with he
  have hee : e * e = e := by
    funext j; simp only [he, letE, Pi.mul_apply, Pi.single_apply]; split_ifs <;> simp
  have hΔe : ∀ δ ∈ W.DelF, W.γA δ e = e := fun δ _ => γA_letE δ (c - 1)
  have hbN : ∀ j, b j ∈ W.N T := fun j => (hb j).1
  have hbΔ : ∀ j, ∀ δ ∈ W.DelF, W.γD T δ (b j) = b j := fun j => (hb j).2
  have hDel : ∀ y : W.DD T, (∀ δ ∈ W.DelF, W.γD T δ y = y) → y ∈ DelS W T :=
    fun y hy => (mem_DelS y).mpr hy
  have hgen : ∀ j, e • b j ∈ NcS W T (c - 1) := by
    intro j
    refine ⟨⟨(W.N T).smul_mem e (hbN j), hDel _ fun δ hδ => ?_⟩, ?_⟩
    · rw [gradNPf_γD_smul, hΔe δ hδ, hbΔ j δ hδ]
    · exact (mem_letS (c - 1) (e • b j)).mpr (by rw [smul_smul, hee])
  let g : Fin r → LcQ W T π' c := fun j => Submodule.Quotient.mk ⟨e • b j, hgen j⟩
  have htop : Submodule.span O (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    induction q using Submodule.Quotient.induction_on with | H x => ?_
    obtain ⟨⟨hxN, hxD⟩, hxL⟩ := x.2
    have hxΔ : (x : W.DD T) ∈ W.NΔ T := ⟨hxN, (mem_DelS _).mp hxD⟩
    have hxe : e • (x : W.DD T) = x := (mem_letS _ _).mp hxL
    obtain ⟨a, haΔ, hxa⟩ := hspan x hxΔ
    choose F hF using fun j => hexp (a j) (haΔ j)
    set κ : Fin r → O := fun j => PowerSeries.constantCoeff (F j (c - 1)) with hκ
    set t : Fin r → LetA O n := fun j => Pi.single (c - 1)
      (PowerSeries.subst (π' (c - 1)) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F j (c - 1))))
      with ht
    have hS : PowerSeries.HasSubst (π' (c - 1)) := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 _)
    have hat : ∀ j, e * a j - algebraMap O (LetA O n) (κ j) * e = π' * t j := by
      intro j
      funext i
      simp only [he, letE, ht, Pi.mul_apply, Pi.sub_apply, Pi.single_apply, Pi.algebraMap_apply]
      split_ifs with hi
      · subst hi
        have e1 : a j (c - 1) = π' (c - 1) * PowerSeries.subst (π' (c - 1))
            (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F j (c - 1))) +
            PowerSeries.C (PowerSeries.constantCoeff (F j (c - 1))) := by
          conv_lhs => rw [hF j (c - 1), PowerSeries.eq_X_mul_shift_add_const (F j (c - 1))]
          rw [PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_X hS,
            PowerSeries.subst_C]
          rfl
        rw [e1, hκ, PowerSeries.algebraMap_apply]
        simp only [Algebra.algebraMap_self, RingHom.id_apply]
        ring
      · simp
    have hdiff : (x : W.DD T) - ∑ j, κ j • (e • b j) = π' • ∑ j, t j • b j := by
      have : (x : W.DD T) = ∑ j, (e * a j) • b j := by
        conv_lhs => rw [← hxe, hxa]
        rw [Finset.smul_sum]; simp only [smul_smul]
      rw [this, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (e * a j) • b j - κ j • (e • b j) =
          (e * a j - algebraMap O (LetA O n) (κ j) * e) • b j by
        rw [sub_smul, mul_smul (algebraMap O (LetA O n) (κ j)) e, algebraMap_smul], hat j, mul_smul]
    have hmem : (x : W.DD T) - ∑ j, κ j • (e • b j) ∈ PiNS W T π' 1 := by
      refine ⟨?_, ?_⟩
      · rw [hdiff]
        exact ⟨∑ j, t j • b j, Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbN j),
          by simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, pow_one, LinearMap.smul_apply, LinearMap.id_apply]⟩
      · refine (DelS W T).sub_mem x.2.1.2 (Submodule.sum_mem _ fun j _ => (DelS W T).smul_mem _ ?_)
        exact (hgen j).1.2
    have : Submodule.Quotient.mk x = ∑ j, κ j • g j := by
      have hy : ∑ j, κ j • g j =
          Submodule.Quotient.mk (∑ j, κ j • (⟨e • b j, hgen j⟩ : ↥(NcS W T (c - 1)))) := by
        rw [← Submodule.mkQ_apply, map_sum]
        simp only [map_smul, Submodule.mkQ_apply, g]
      rw [hy, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub,
        Submodule.coe_sum]
      simpa only [Submodule.coe_smul] using hmem
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨⟨Finset.univ.image g, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact htop⟩⟩

end Local

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem lcq_finite (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    Module.Finite ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, -, hm₀⟩, -⟩ := h9W T hT hs1 hp
  obtain ⟨r, b, hbΔ, -, hspan⟩ := hm₀.1
  have hs : 1 ≤ sK l K := frobpin_sK_pos hl K LL hG
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    rw [hw]
    simp only [Pi.mul_apply, Pi.pow_apply, letπ, map_mul, map_pow, PowerSeries.constantCoeff_X,
      zero_pow (by omega : sK l K ≠ 0), mul_zero]
  have hexp : ∀ a ∈ ((HW l).W K 1 LL hG).AΔ, ∃ F : ZMod (finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL),
      ∀ i, a i = PowerSeries.subst (π' i) (F i) := fun a ha => (hR.2.1 a ha).exists
  exact lcq_finite_local hπ0 hexp r b hbΔ hspan

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem u2rank_of_ring (hR : Formalism.MainNotions.N.Ln34.SecondRingHypothesis) : Formalism.MainNotions.N.Ln34.SecondRankHypothesis := by
  intro D HW F Cm CA CB CK hA hML l _ hl K LL hG π' E hπ T h' hh' hc hj c
  haveI : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  exact u2rank_local (W := (HW l).W K 1 LL hG) (T := T) (π' := π') (c := c)
    (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')
    (hML l hl K LL hG π' E hπ h' hh' T hc hj c)
    (hR D HW F Cm CA CB CK hA l hl K LL hG π' E hπ h' hh' c)
    (lcq_finite D HW F Cm hA.1 l hl K LL hG π' E hπ T hc c)

end Formalism.MainNotions.N.Ln34.RankBounds

end
