import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridWeil

variable {D : D7}

theorem denseRange_units_inf (F : Type) [Field F] [NumberField F] :
    DenseRange (Units.map (algebraMap F (InfiniteAdeleRing F)).toMonoidHom) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing F)ˣ → InfiniteAdeleRing F) :=
    Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace F, v.Completion)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact v.ne_zero hk
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem triv_base {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (hF : χ.TrivOn D.host.F)
    (a : (AF D.host.F)ˣ) : c (idF D a) = 1 := by
  let i : (Ainf D.host.F)ˣ →* (AF D.host.F)ˣ := Units.map (MonoidHom.inl (Ainf D.host.F) (Af D.host.F))
  let p : (AF D.host.F)ˣ →* (Ainf D.host.F)ˣ := Units.map (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))
  have key : ∀ a, c (idF D a) = c (idF D (i (p a))) := fun a => by
    let b : (AF D.host.F)ˣ := Units.map ((MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))) a
    have e : a = i (p a) * b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    conv_lhs => rw [e, map_mul, map_mul, GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ h hF b rfl, mul_one]
  have c1 : Continuous (idF D) := Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D)))
  have c2 : Continuous i := Continuous.units_map _ (continuous_id.prodMk continuous_const)
  rw [key]
  generalize p a = z
  refine (denseRange_units_inf D.host.F).induction_on z
    (isClosed_eq (h.1.1.comp (c1.comp c2)) continuous_const) fun k => ?_
  refine (key (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom k)).symm.trans ?_
  rw [← h.1.2 (Formalism.L2.Host.upF D.host.F k)]
  congr 1
  exact Units.ext (GlobalTheory.BaseIdeleTriv.algebraMap_tmul_one (k : D.host.F))

theorem attChr_ok {c η : (AE D)ˣ →* Circle} (hc : IsHeckeChar D c) (h0 : ∀ a, c (idF D a) = 1) (hη : IsHeckeChar D η)
    (h1 : IsEta D (η.comp (idF D))) (n : ℕ) :
    IsHeckeChar D (Formalism.IndefR.Lift.attChr c η n) ∧ ResEta D (Formalism.IndefR.Lift.attChr c η n) n := by
  have hsq : ∀ a, η (idF D a) * η (idF D a) = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self h1
  unfold Formalism.IndefR.Lift.attChr
  split_ifs with hn
  · refine ⟨⟨hc.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hc.2, hη.2, inv_one, mul_one]⟩,
      ⟨_, h1⟩, fun η' h' a => ?_⟩
    obtain ⟨k, rfl⟩ := hn
    rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h' h1, MonoidHom.mul_apply, MonoidHom.inv_apply, h0,
      MonoidHom.comp_apply, pow_succ, pow_mul, pow_two, hsq, one_pow, inv_eq_of_mul_eq_one_right (hsq a)]
  · refine ⟨hc, ⟨_, h1⟩, fun η' h' a => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.1 hn
    rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h' h1, h0, MonoidHom.comp_apply, pow_add, ← mul_pow, hsq, one_pow]

open scoped ComplexOrder in

theorem exists_cartan {V : HSp D} (hV : V.SigOK) (τ : D.what₂.Tau) :
    ∃ s P : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsCartanInv (gramAt D V τ) s ∧ ∃ ε : Fin V.rank → Bool,
      Pᴴ * gramAt D V τ * P = Formalism.REAL.Jm ε ∧ s * P = P * Formalism.REAL.Jm ε := by
  obtain ⟨ε, fr, h⟩ := GlobalTheory.Published.AutFin.exists_isFrameFam V hV
  obtain ⟨⟨u, hu⟩, hG⟩ := h τ
  set J := Formalism.REAL.Jm (ε τ) with hJ
  have J1 : J * J = 1 := by
    rw [hJ, Formalism.REAL.Jm, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have J2 : Jᴴ = J := by
    rw [hJ, Formalism.REAL.Jm, diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply]
    split_ifs <;> simp
  set A := fr τ
  set B : Matrix (Fin V.rank) (Fin V.rank) ℂ := (u⁻¹).1
  have AB : A * B = 1 := by rw [← hu]; exact u.mul_inv
  have BA : B * A = 1 := by rw [← hu]; exact u.inv_mul
  have AB' : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, A * (B * X) = X := fun X => by rw [← Matrix.mul_assoc, AB, Matrix.one_mul]
  have BA' : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Bᴴ * (Aᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, AB, conjTranspose_one, Matrix.one_mul]
  have J1' : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, J * (J * X) = X := fun X => by rw [← Matrix.mul_assoc, J1, Matrix.one_mul]
  rw [← hG]
  refine ⟨B * J * A, B, ⟨?_, ?_, ?_⟩, ε τ, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, AB', J1', BA]
  · simp only [conjTranspose_mul, J2, Matrix.mul_assoc, AB', BA', J1']
  · simp only [Matrix.mul_assoc, AB', J1']
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ⟨u, hu⟩)
  · simp only [Matrix.mul_assoc, AB, BA', Matrix.mul_one, hJ]
  · simp only [Matrix.mul_assoc, AB, Matrix.mul_one, hJ]

theorem hasSignature_neg {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (-J) q p := by
  obtain ⟨e, P, hP⟩ := h
  let s := Equiv.sumComm (Fin p) (Fin q)
  refine ⟨e.trans s, Units.map (Matrix.reindexAlgEquiv ℂ ℂ s).toRingHom.toMonoidHom P, ?_⟩
  have e1 : Formalism.UG.Jpq q p = -(Formalism.UG.Jpq p q).submatrix s.symm s.symm := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Formalism.UG.Jpq, s]
  rw [e1, ← hP, ← submatrix_mul_equiv _ _ _ s.symm, ← submatrix_mul_equiv _ _ _ s.symm, ← Matrix.neg_mul, ← Matrix.mul_neg]
  rfl

theorem sigOK_neg {V : HSp D} (h : V.SigOK) : (negSp V).SigOK := fun τ => by
  have e : (negSp V).gram.map τ = -V.gram.map τ := Matrix.ext fun i j => map_neg τ _
  rw [e]
  exact hasSignature_neg (h τ)

section Coset

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_den {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (hM : M.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, ∀ i j, ∃ o : 𝓞 D.host.E, (o : D.host.E) = N • x i j := by
  obtain ⟨s, rfl⟩ := hM
  let O : AddSubgroup D.host.E := (algebraMap (𝓞 D.host.E) D.host.E).range.toAddSubgroup
  obtain ⟨k, hk, hO⟩ := GlobalTheory.PlaceVec.exists_common_nsmul O (fun p : s × Fin m × Fin n => p.1.1 p.2.1 p.2.2) fun p => by
    obtain ⟨d, hd, h⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral D.host.E (p.1.1 p.2.1 p.2.2)
    exact ⟨d, hd, by rw [nsmul_eq_mul]; exact h⟩
  refine ⟨k, hk, fun x hx i j => ?_⟩
  show k • x i j ∈ O
  induction hx using Submodule.span_induction with
  | mem x hx => exact hO (⟨x, hx⟩, i, j)
  | zero => rw [Matrix.zero_apply, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_apply, smul_add]; exact add_mem hx hy
  | smul c x _ hx =>
    obtain ⟨o, ho⟩ := hx
    refine ⟨c * o, ?_⟩
    rw [map_mul, ho, Matrix.smul_apply, smul_comm, Algebra.smul_def c]

theorem exists_nsmul_hatMx (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (M : Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E)) (hM : M.FG) :
    ∃ K : ℕ, 0 < K ∧ ∀ w ∈ hatMx M,
      K • w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨N, hN, h⟩ := exists_den M hM
  obtain ⟨k, hk, h'⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT
  refine ⟨k * N, mul_pos hk hN, fun w hw => ?_⟩
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    rw [mul_smul]
    refine h' _ (Matrix.ext fun i j => ?_) fun i j => ?_
    · have h0 : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j) = 0 := TensorProduct.zero_tmul _ _
      exact ((infPart D).toAddMonoidHom.map_nsmul N (pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j)).trans
        ((congrArg (N • ·) h0).trans (nsmul_zero N))
    · obtain ⟨o, ho⟩ := h x hx i j
      have h1 := GlobalTheory.PlaceVec.tmul_mem_int (F := D.host.F) hα o
      rw [ho, ← TensorProduct.smul_tmul'] at h1
      rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]
      exact h1
  | zero => rw [nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem exists_nsmul_latO (hS : IsSelfDualC S ΛS) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ K : ℕ, 0 < K ∧ ∀ w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      K • w ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
  obtain ⟨d, hd, hA⟩ := D.host.AA.isFractional
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨c, hc⟩ : d ∣ (Ideal.absNorm (Ideal.span {d}) : 𝓞 D.host.E) := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)
  have p1 : 0 < Ideal.absNorm (Ideal.span {d}) := Nat.pos_of_ne_zero fun h =>
    hd0 (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h))
  have p2 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  generalize Ideal.absNorm (Ideal.span {d}) = N at hc p1
  refine ⟨Ideal.absNorm 𝔪 * N, mul_pos p2 p1, fun w hw => ?_⟩
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨o, ho⟩ := hA a ha
    let x : Matrix (Fin T.rank) (Fin S.rank) D.host.E := Matrix.of fun i j => a * t i * ∑ k, star (s k) * S.gram k j
    have hx : (N : 𝓞 D.host.E) • x ∈ homLat ΛS ΛT := fun y hy => by
      obtain ⟨b, hb⟩ := (hS.2 y).1 hy s hs
      have e : ((N : 𝓞 D.host.E) • x) *ᵥ y = (c * o * b) • t := by
        funext i
        have hb' : algebraMap (𝓞 D.host.E) D.host.E b = ∑ j, (∑ k, star (s k) * S.gram k j) * y j := by
          rw [show algebraMap (𝓞 D.host.E) D.host.E b = _ from hb, Finset.sum_comm]
          simp only [Finset.sum_mul]
        rw [smul_mulVec, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, hc, map_mul, map_mul, map_mul,
          ho, hb', Algebra.smul_def]
        simp only [x, mulVec, dotProduct, of_apply, mul_assoc, ← Finset.mul_sum]
        ring
      rw [e]
      exact ΛT.smul_mem _ ht
    refine AddSubgroup.subset_closure ⟨α, hα, _, Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hx, ?_⟩
    ext i j
    simp only [Nat.cast_smul_eq_nsmul, smul_smul, Matrix.smul_apply, of_apply, TensorProduct.tmul_smul, x]
  | zero => rw [nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem isSBHalf_cosInd (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    {e : AE D} (he : e * e = e) (hinf : infPart D e = 0) (κ : Cos ΛS ΛT 𝔪) :
    IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (cosInd e κ) := by
  obtain ⟨K, hK, h1⟩ := exists_nsmul_hatMx hS.1 hT.1 (homLat ΛS ΛT) (Module.Finite.iff_fg.1 (homLat_fg hS.1 hT.1.fg))
  obtain ⟨K', hK', h2⟩ := exists_nsmul_latO (T := T) (ΛT := ΛT) hS h𝔪
  have hne : ∀ t, cosInd e κ t ≠ 0 → t ∈ cosSet e κ := fun t ht => Set.mem_of_indicator_ne_zero ht
  refine ⟨fun t ht => (hne t ht).1, K * K', mul_pos hK hK', fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have hm : (K * K') • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
      rw [mul_smul]; exact nsmul_mem (h2 u hu) K
    have hh : IsHalf e (t + (K * K') • u) ↔ IsHalf e t := by
      rw [GlobalTheory.PlaceModel.isHalf_iff, GlobalTheory.PlaceModel.isHalf_iff]
      exact add_mem_cancel_right (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu') _)
    have hiff : t + (K * K') • u ∈ cosSet e κ ↔ t ∈ cosSet e κ := by
      refine and_congr hh (exists_congr fun x₀ => and_congr_right fun _ => ?_)
      rw [add_sub_right_comm]
      exact add_mem_cancel_right hm
    unfold cosInd
    by_cases ht : t ∈ cosSet e κ
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hiff.2 ht)]
      rfl
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem fun h => ht (hiff.1 h)]
  · obtain ⟨-, x₀, -, h⟩ := hne t ht
    have a1 := h1 _ (AddSubgroup.closure_mono (by
      rintro _ ⟨α, hα, x, hx, rfl⟩
      exact ⟨α, hα, x, Submodule.smul_le_right hx, rfl⟩) h)
    have a2 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])) _
      (h1 _ (AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), x₀.1, x₀.2, rfl⟩))
    have e1 : e • (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D) =
        e • (Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] x₀.1 i j : WO S T) := by
      ext i j
      show e * _ = e * _
      refine GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, RingHom.map_mul, hinf, zero_mul, zero_mul]) ?_
      rw [RingHom.map_mul, RingHom.map_mul]
      rfl
    rw [smul_comm, ← e1] at a2
    have a3 := add_mem a1 a2
    rw [← nsmul_add, sub_add_cancel] at a3
    rw [mul_comm, mul_smul]
    exact nsmul_mem a3 _

end Coset

theorem exists_weil : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (sc : Consts) (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ W : G.Weil, W.ψ = ψ := by
  intro hW D T L μ0 hL sc G ψ hψ
  classical
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hV : ∀ X : Node, X.InRange D.R.m → (G.V X).SigOK ∧ IsSelfDualC (G.V X) (G.Λ X) := fun X hX => by
    by_cases h0 : ∀ j, X ≠ .grid 0 j
    · exact ⟨(G.isV hX h0).sigOK, (G.isV hX h0).sd⟩
    · push Not at h0
      obtain ⟨j, rfl⟩ := h0
      exact ⟨(GlobalTheory.ChiGrid.colY_isV D T L μ0 hL j hX.2).sigOK, (GlobalTheory.ChiGrid.colY_isV D T L μ0 hL j hX.2).sd⟩
  have h1 : ∀ (X : Node) (τ : D.what₂.Tau), ∃ s P : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ, X.InRange D.R.m →
      IsCartanInv (gramAt D (G.V X) τ) s ∧ ∃ ε : Fin (G.V X).rank → Bool,
        Pᴴ * gramAt D (G.V X) τ * P = Formalism.REAL.Jm ε ∧ s * P = P * Formalism.REAL.Jm ε := fun X τ => by
    by_cases hX : X.InRange D.R.m
    · obtain ⟨s, P, h⟩ := exists_cartan (hV X hX).1 τ
      exact ⟨s, P, fun _ => h⟩
    · exact ⟨1, 1, fun h => absurd h hX⟩
  choose s P hs using h1
  have hη := GlobalTheory.Mem.EtaTilde.isEta_res D _ _ hL.eta L.C.isEta
  have hchi : ∀ i, i + 1 ≤ D.R.m → IsHeckeChar D (G.ch.chi (D.R.m - i)) ∧ ∀ a, G.ch.chi (D.R.m - i) (idF D a) = 1 :=
    fun i hi => ⟨(G.ch.chi_eq _ (by omega) (by omega)).1,
      triv_base (G.ch.chi_eq _ (by omega) (by omega)) (G.ch.triv _ (by omega) (by omega))⟩
  have hmu : ∀ t j, j + 1 ≤ D.R.m → IsHeckeChar D (L.mu t (j + 1)) ∧ ∀ a, L.mu t (j + 1) (idF D a) = 1 := fun t j hj => by
    have a1 := hL.mu0 ⟨j, hj⟩
    have a2 := hL.xi t
    refine ⟨⟨a1.1.1.mul a2.1.1, fun x => ?_⟩, fun a => ?_⟩
    · exact (congrArg₂ (· * ·) (a1.1.2 x) (a2.1.2 x)).trans (mul_one _)
    · exact (congrArg₂ (· * ·) (triv_base a1 (L.C.isMu0 _).triv a) (triv_base a2 (hL.xi_triv t) a)).trans (mul_one _)
  have hchr : ∀ p : Pair T, p.InRange D.R.m → IsHeckeChar D (G.chr p) ∧ ∀ a, G.chr p (idF D a) = 1 := by
    rintro (⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩) hp
    · exact hchi i hp.1
    · exact hmu t j hp.2
    · exact hchi i hp
    · exact hmu t j hp
  have h2 : ∀ p : Pair T, ∃ om : GA D (G.pS p) × GA D (G.pT p) →* Module.End ℂ (WO (G.pS p) (G.pT p) → ℂ),
      p.InRange D.R.m → IsWeilDatumO ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) om := fun p => by
    by_cases hp : p.InRange D.R.m
    · have a1 := attChr_ok (hchr p hp).1 (hchr p hp).2 hL.eta.1 hη
      obtain ⟨om, h⟩ := hW D ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) hψ (a1 _).1 (a1 _).1 (a1 _).2 (a1 _).2
      exact ⟨om, fun _ => h⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose om hom using h2
  have r1 : ∀ i, i < D.R.m → (Node.grid (i + 1) 0).InRange D.R.m := fun i hi => ⟨hi, Nat.zero_le _⟩
  have r0 : ∀ i, i < D.R.m → (Node.grid i 0).InRange D.R.m := fun i hi => ⟨hi.le, Nat.zero_le _⟩
  have h3 : ∀ i, ∃ f : WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ, i < D.R.m →
      IsVacO ψ θ _ _ (G.cartS s (.chi i 0)) (G.onT s (.chi i 0))
        (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) f := fun i => by
    by_cases hi : i < D.R.m
    · obtain ⟨f, h⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.cartS s (.chi i 0))
        (G.onT s (.chi i 0)) (sigOK_neg (hV _ (r1 i hi)).1) (hV _ (r0 i hi)).1
        (fun τ => isCartanInv_neg (hs _ τ (r1 i hi)).1) (fun τ => (hs _ τ (r0 i hi)).1) _ _
        (isSelfDualC_neg (hV _ (r1 i hi)).2) (hV _ (r0 i hi)).2
      exact ⟨f, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose vac hvac using h3
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h4 : ∀ i (κ : G.CosAt i), ∃ f : WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ, i < D.R.m →
      IsThetaAt ψ (symplO _ _) (heisO ψ _ _) e
        (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1
        (vac i) (cosInd e κ) f := fun i κ => by
    by_cases hi : i < D.R.m
    · have dS := isSelfDualC_neg (hV _ (r1 i hi)).2
      have dT := (hV _ (r0 i hi)).2
      have e1 := GlobalTheory.PlaceVec.idemSum_mul_self he
      have e2 := GlobalTheory.PlaceVec.idemSum_infPart he
      obtain ⟨f, h⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ dS dT e1 e2
        (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ _ _ _ _ dS dT _ e he _ (hvac i hi).2.theta (hvac i hi).2.lat).1
        (isSBHalf_cosInd dS dT (G.pl.modul_ne_bot sc) e1 e2 κ)
      exact ⟨f, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose cv hcv using h4
  exact ⟨⟨ψ, hψ, θ, hθ, s, fun X hX τ => (hs X τ hX).1, P, fun X hX τ => (hs X τ hX).2, om, hom, vac, hvac, cv,
    e, he, fun i hi κ => hcv i κ hi⟩, rfl⟩

end GlobalTheory.GridWeil

end
