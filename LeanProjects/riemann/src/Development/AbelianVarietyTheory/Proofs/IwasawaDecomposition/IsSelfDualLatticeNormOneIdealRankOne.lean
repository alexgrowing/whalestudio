import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColRecCEvBijective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubStdL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90USurjective

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

theorem mem_iff_trace {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (Xg : Finset (G → K))
    (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ) {χ : G → K} (hχ : IsAbsIrrChar χ) :
    χ ∈ Xg ↔ ∑ g, (idemOf Xg).coeff g * χ g = χ 1 := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h1 : χ 1 ≠ 0 := by
    intro h0
    have h := conv_char hχ hχ
    obtain ⟨n, ρ, hi, hρ⟩ := hχ
    have e := hρ 1
    rw [h0, map_zero, Representation.char_one, Module.finrank_fin_fun, Nat.cast_eq_zero] at e
    subst e
    exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hterm : ∀ ψ ∈ Xg, ∑ g, (chiIdem ψ).coeff g * χ g = if ψ = χ then χ 1 else 0 := by
    intro ψ hψ
    have h := conv_char (hXg ψ hψ) hχ 1
    simp only [mul_one] at h
    have e : ∑ g, (chiIdem ψ).coeff g * χ g = ψ 1 / (Fintype.card G : K) * ∑ g, ψ g⁻¹ * χ g := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by rw [coeff_chiIdem, mul_assoc]
    rw [e]
    split_ifs at h ⊢ with hc
    · rw [mul_right_cancel₀ h1 h, hc]
      field_simp
    · rw [(mul_eq_zero.1 h).resolve_right h1, mul_zero]
  have hsum : ∑ g, (idemOf Xg).coeff g * χ g = if χ ∈ Xg then χ 1 else 0 := by
    unfold idemOf
    simp only [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  rw [hsum]
  split_ifs with hc
  · exact iff_of_true hc rfl
  · exact iff_of_false hc h1.symm

theorem mem_iff_XgE {K G H : Type} [Field K] [CharZero K] [Group G] [Fintype G] [Group H] [Fintype H] (σ : K →+* ℂ) (eG : G ≃* H)
    (e : MonoidAlgebra ℂ H) (Xg : Finset (G → K)) (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (he : ∀ g, σ ((idemOf Xg).coeff g) = e.coeff (eG g)) (χ : G → K) :
    χ ∈ Xg ↔ (fun g => χ (eG.symm g)) ∈ XgE σ e := by
  rw [mem_XgE, isAbsIrrChar_comp_iff eG.symm, ← Equiv.sum_comp eG.toEquiv]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.symm_apply_apply, map_one, ← he, ← map_mul, ← map_sum]
  rw [σ.injective.eq_iff]
  exact ⟨fun h => ⟨hXg χ h, (mem_iff_trace Xg hXg (hXg χ h)).1 h⟩, fun h => (mem_iff_trace Xg hXg h.1).2 h.2⟩

theorem exists_coord {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) {n d : ℕ}
    (Ψ : (Fin n → K) ≃ₗ[K] (Fin d → K)) (j : (Fin n → K) →ₛₗ[σ] W)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ ι : W ≃ₗ[ℂ] (Fin d → ℂ), ∀ y, ι (j y) = fun a => σ (Ψ y a) := by
  classical
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk li sp.ge
  have hb : ∀ y, b.equivFun (j y) = fun i => σ (y i) := by
    intro y
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [pi_eq_sum_univ' y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.mk_apply]
  let A := LinearMap.toMatrix' Ψ.toLinearMap
  let A' := LinearMap.toMatrix' Ψ.symm.toLinearMap
  have h1 : A * A' = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : A' * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  let E : (Fin n → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofLinear (Matrix.toLin' (A.map σ)) (Matrix.toLin' (A'.map σ))
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, h1]; simp) (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, h2]; simp)
  refine ⟨b.equivFun.trans E, fun y => ?_⟩
  rw [LinearEquiv.trans_apply, hb]
  funext a
  show (A.map σ).mulVec (σ ∘ y) a = _
  rw [← RingHom.map_mulVec]
  exact congrArg σ (congrFun (LinearMap.toMatrix'_mulVec Ψ.toLinearMap y) a)

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem rowCast_lin {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
    (Λ' : LevFam X.E X.K (R.N R.m - 1) SG') (hΛ : Λ' = e ▸ A) :
    ((formGSD (rowVal W SG') Λ').Ok → (rowGSD W A).Ok) ∧
      ∃ L : (formGSD (rowVal W SG') Λ').EqFun ≃ₗ[X.K] (rowGSD W A).EqFun, ∀ F, L F = rowCast W e A Λ' hΛ F := by
  subst hΛ
  subst e
  exact ⟨id, LinearEquiv.refl _ _, fun _ => rfl⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs)

include hX in

theorem rowG_ok (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) : (rowGSD W (rowTyG Ch P).inv).Ok :=
  (rowCast_lin W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)).1 (mtildeOk W Ch sel mu hX P)

theorem exists_lvlEquiv : ∃ Φ : (Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim
      (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) ≃ₗ[X.K] MtildeV W Ch sel mu P,
    ∀ y, ∃ hK : (Φ y).1 ∈ (mtildeKGSD W Ch sel mu).EqFun,
      (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) ⟨(Φ y).1, hK⟩ =
        (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
          (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y) := by
  set h := mtildeKOk W Ch sel mu hX
  have hr : LinearMap.range ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVecLin =
      (MtildeKCSD W Ch sel mu h).lvlPart (g0Act W Ch sel mu h) P.grp P.chr :=
    (image_idempotent_spec X.K _ _).2.trans (level_part_spec X.K _ _ _ _ _)
  let c := (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec
  let f0 := c.symm.toLinearMap ∘ₗ ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVecLin
  have hf0 : ∀ y, c (f0 y) = ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVec y :=
    fun y => c.apply_symm_apply _
  have hm : ∀ y, ((mtildeKGSD W Ch sel mu).EqFun.subtype ∘ₗ f0) y ∈ (mtildeGSD W Ch sel mu P).EqFun := fun y => by
    refine (mem_lvlPartX_iff W Ch sel mu P h (f0 y)).1 ?_
    rw [← hr]
    exact ⟨y, (hf0 y).symm⟩
  let f := LinearMap.codRestrict _ _ hm
  have hinj : Function.Injective f := fun y y' e => by
    have e1 : f0 y = f0 y' := Subtype.ext (congrArg Subtype.val e :)
    exact (image_idempotent_spec X.K _ _).1 ((hf0 y).symm.trans ((congrArg c e1).trans (hf0 y')))
  have hsurj : Function.Surjective f := fun x => by
    obtain ⟨hK, -⟩ := (mem_MtildeV_iff W Ch sel mu P x.1).1 x.2
    have h1 := (mem_lvlPartX_iff W Ch sel mu P h ⟨x.1, hK⟩).2 x.2
    rw [← hr] at h1
    obtain ⟨y, hy⟩ := h1
    have e1 : f0 y = ⟨x.1, hK⟩ := c.injective ((hf0 y).trans hy)
    exact ⟨y, Subtype.ext (congrArg Subtype.val e1 :)⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun y => ⟨(f0 y).2, ?_⟩⟩
  rw [← hf0]
  exact (LinearEquiv.symm_apply_apply _ _).symm

theorem exists_read (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (σ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (j : (Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim
      (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) →ₛₗ[σ] V)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ ι : V ≃ₗ[ℂ] (Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ), ∀ y,
      ∃ (F' : (mtildeKGSD W Ch sel mu).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun),
        (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) F' =
          (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
            (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y) ∧
        ι (j y) = zOfRow W Ch sel mu hQ P σ hM ⟨F'.1, hm⟩ := by
  obtain ⟨Φ, hΦ⟩ := exists_lvlEquiv W Ch sel mu hX P
  obtain ⟨L, hL⟩ := (rowCast_lin W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)).2
  obtain ⟨ι, hι⟩ := exists_coord σ ((Φ.trans L).trans ((rowGSD W (rowTyG Ch P).inv).hB hM).equivFun) j li sp
  refine ⟨ι, fun y => ?_⟩
  obtain ⟨hK, e⟩ := hΦ y
  refine ⟨⟨(Φ y).1, hK⟩, (Φ y).2, e, (hι y).trans ?_⟩
  unfold zOfRow zOfRow0
  rw [← hL]
  rfl

end Rows

section Weights

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem nuT_eq (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : Tau B.R) (r : Fin (B.R.N i)) :
    ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = (B.wts.nuW u (i + 1) τ).w r := by
  have e1 : ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℝ) = DV.nuRow (I.rec7 l Z) u (i + 1) τ r := (nu_t_identity (I.rec7 l Z) u i hi τ r).1
  have e2 := GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2
  have e3 := B.wts.nuW_eq u hi τ r
  have e4 := lamOf_wtN (B.wts.hc u τ) hi.le r
  have key : (((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) : ℝ) = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
    rw [Int.cast_natCast, e1, e2, ← Rat.cast_intCast, e3]
    unfold Wts.lamN at e3 ⊢
    rw [e4]
    rfl
  exact_mod_cast key

theorem wtTie_base {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) :
    t.WtTie (fun u i τ => B.wts.lamTrue u i τ) (fun u i τ => (B.wts.lamTrue u i τ).detShift)
      (fun u i τ => nuLast (Pr := B.primes X) B.wts u i τ) := by
  intro (u : B.Word) μ i hi
  have hi' : i < B.R.m := hi
  have hN : 0 < B.R.N i := B.R.N_pos i
  have hN' : 0 < B.R.N (i + 1) := B.R.N_pos (i + 1)
  have hlt : B.R.N i < B.R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  have d0 : ∀ τ, (B.wts.lamTrue u i τ).detShift = (B.wts.lamTrue u i τ).w ⟨B.R.N i - 1, by omega⟩ := fun τ => dif_pos hN
  have d' : ∀ τ, (B.wts.lamTrue u (i + 1) τ).detShift = (B.wts.lamTrue u (i + 1) τ).w ⟨B.R.N (i + 1) - 1, by omega⟩ :=
    fun τ => dif_pos hN'
  have dn : ∀ τ, (B.wts.nuW u (i + 1) τ).detShift = (B.wts.nuW u (i + 1) τ).w (⟨B.R.N i - 1, by omega⟩ : Fin (B.R.N i)) :=
    fun τ => dif_pos hN
  have hs : ∀ (τ : Tau B.R) (r : Fin (B.R.N i)),
      (B.wts.nuW u (i + 1) τ).w r = (B.wts.lamTrue u i τ).w r + ((I.rec7 l Z).chTw u μ).sSharp i τ := fun τ r => by
    have e1 := B.wts.nuW_eq_true u hi' τ r
    have e2 : ((((I.rec7 l Z).chTw u μ).sSharp i τ : ℤ) : ℚ) = sExp' B.R ((B.wts.hc u τ).e ⟨i, hi'⟩) (i + 1) :=
      ((I.rec7 l Z).chTw u μ).sSharp_eq i hi τ
    rw [← e2] at e1
    exact_mod_cast e1
  have hl : ∀ τ, ((nuLast (Pr := B.primes X) B.wts u i τ : ℕ) : ℤ) =
      (B.wts.lamTrue u i τ).detShift + ((I.rec7 l Z).chTw u μ).sSharp i τ := fun τ => by
    rw [nuLast_eq (Pr := B.primes X) B.wts u i hi' τ, dn, hs, d0]
  refine ⟨fun (τ : Tau B.R) (r : Fin (B.R.N i)) => ?_, fun τ => (hl τ).symm, fun (τ : Tau B.R) => ?_, jet_in_weight_space_chain (Pr := B.primes X) B.wts u hi'⟩
  · have e1 := nuT_eq I l Z u hi' τ r
    have e2 := hs τ r
    have e3 := hl τ
    have hanti : (B.wts.lamTrue u i τ).detShift ≤ (B.wts.lamTrue u i τ).w r := by
      refine (d0 τ).trans_le ?_
      exact (B.wts.lamTrue u i τ).anti (by show r.1 ≤ B.R.N i - 1; have : r.1 < B.R.N i := r.2; omega)
    show ((B.wts.lamTrue u i τ).w r - (B.wts.lamTrue u i τ).detShift).toNat + nuLast (Pr := B.primes X) B.wts u i τ = nuT (I.rec7 l Z) u i τ r
    omega
  · have e1 := B.wts.lamTrue_new u hi' τ ⟨B.R.N (i + 1) - 1, by omega⟩ (by show ¬ B.R.N (i + 1) - 1 < B.R.N i; omega)
    have e2 : ((((I.rec7 l Z).chTw u μ).sDiv i τ : ℤ) : ℚ) = sExp B.R ((B.wts.hc u τ).e ⟨i, hi'⟩) (i + 1) :=
      ((I.rec7 l Z).chTw u μ).sDiv_eq i hi τ
    rw [← e2] at e1
    refine (d' τ).trans ?_
    exact_mod_cast e1

end Weights

section Chi

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem isSelfDualLattice_normOne_ideal_rankOne {D : D7} {𝔞 : TaylorLogMetric.IdE D} (h : TaylorLogMetric.N1 D 𝔞) :
    IsSDLat D.host.E 1 (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) := by
  obtain ⟨𝔟, hb, hab⟩ := h
  have hc : ∀ x : D.host.E, star x = D.host.conj x := fun x => bridge_star_holds D.R D.host x
  have hfg : 𝔞.FG := Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one 𝔟 hab)
  refine ⟨Submodule.fg_pi fun _ => hfg, ?_, fun y => ?_⟩
  · obtain ⟨x, hx, h0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
      by_contra hn
      push Not at hn
      have : 𝔞 = ⊥ := (Submodule.eq_bot_iff _).2 hn
      rw [this, Submodule.bot_mul] at hab
      have h1 : (1 : D.host.E) ∈ (1 : TaylorLogMetric.IdE D) := Submodule.one_le.1 le_rfl
      rw [← hab] at h1
      exact one_ne_zero ((Submodule.mem_bot _).1 h1)
    rw [eq_top_iff]
    intro v _
    have : v = (v 0 / x) • (fun _ : Fin 1 => x) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [h0]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span fun _ _ => hx)
  · constructor
    · intro hy x hx
      have h1 : y 0 * star (x 0) ∈ 𝔞 * 𝔟 := Submodule.mul_mem_mul (hy 0 trivial) ((hb _).2 (by rw [← hc, star_star]; exact hx 0 trivial))
      rw [hab, Submodule.mem_one] at h1
      obtain ⟨r, hr⟩ := h1
      exact ⟨r, by rw [hr]; simp [stdH, mul_comm]⟩
    · intro hy i _
      rw [Subsingleton.elim i 0]
      have h1 : Submodule.span (𝓞 D.host.E) {y 0} * 𝔟 ≤ 1 := by
        rw [Submodule.span_singleton_mul]
        intro z hz
        obtain ⟨b, hb', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
        obtain ⟨r, hr⟩ := hy (fun _ => star b) fun _ _ => by rw [hc]; exact (hb b).1 hb'
        exact Submodule.mem_one.2 ⟨r, by rw [hr]; simp [stdH, mul_comm]⟩
      have h2 : Submodule.span (𝓞 D.host.E) {y 0} ≤ 𝔞 := by
        calc Submodule.span (𝓞 D.host.E) {y 0} = 𝔞 * (Submodule.span (𝓞 D.host.E) {y 0} * 𝔟) := by
              rw [mul_left_comm, hab, mul_one]
          _ ≤ 𝔞 * 1 := mul_le_mul_right h1 𝔞
          _ = 𝔞 := mul_one _
      exact h2 (Submodule.mem_span_singleton_self _)

theorem detId_rank_one {R : Ranks} (H : Host R) (𝔞 : Submodule (𝓞 H.E) H.E) :
    Th.detId H (Th.stdL H 1) (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) = 𝔞 := by
  rw [GlobalTheory.Mem.ChiDet.detId_stdL]
  unfold GlobalTheory.Mem.Chr.detSub
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Matrix.det_unique]
    exact hx _ _ trivial
  · intro a ha
    exact Submodule.subset_span ⟨fun _ _ => a, fun _ _ _ => ha, by rw [Matrix.det_unique]; rfl⟩

theorem chiRec_eq_chi {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    (𝔞 : TaylorLogMetric.IdE (I.rec7 l Z)) (h : TaylorLogMetric.N1 (I.rec7 l Z) 𝔞) : TaylorLogMetric.chiRec (I.rec7 l Z) idl 𝔞 = I.chi 𝔞 := by
  have h1 : TaylorLogMetric.N1 (I.rec7 l Z) 1 := by
    have := RcHyp.n1_span_unitary (D := I.rec7 l Z) 1
    rwa [OneMemClass.coe_one, ← Submodule.one_eq_span] at this
  have hs := isSelfDualLattice_normOne_ideal_rankOne h
  have h2 := hidl.2.2.2.2 1 ⟨_, isSelfDualLattice_normOne_ideal_rankOne h1⟩ ⟨_, hs⟩
  have h3 : TaylorLogMetric.detId (I.rec7 l Z) (Submodule.pi Set.univ fun _ : Fin 1 => (1 : TaylorLogMetric.IdE (I.rec7 l Z)))
      (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) = 𝔞 := detId_rank_one B.host 𝔞
  have h4 := h2.trans h3
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (relDetQ B.host I.SQ 1 (Th.stdL B.host 1) (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞))
  have h5 : idl (QuotientGroup.mk x) = 𝔞 := (congrArg idl hx).trans h4
  have h6 := GlobalTheory.Mem.ChiDet.tildeD_eq_chiId B.R B.host I.C.chiPsi I.C.isChi 1 (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) ⟨hs.1, hs.2.1⟩
    (toDtT B.host I.SQ x) (congrArg (toDtTMod B.host I.SQ) hx)
  replace h6 := h6.trans (congrArg (chiId I.C.chiPsi) (detId_rank_one B.host 𝔞))
  refine ((congrArg _ h5.symm).trans (TaylorLogMetric.chiRec_idl _ _ hidl.1 _)).trans (Eq.trans ?_ h6)
  show ((tildeQ B.host I.SQ I.C.chiPsi x : ℂˣ) : ℂ) = _
  rw [tildeQ_eq_comp B.host I.SQ (KD_le_ker_of_isChiPsi I.C.isChi)]
  rfl

theorem ker_chi_eq {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) :
    ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → t.χ 𝔞 = I.chi 𝔞 := fun 𝔞 h => by
  rw [t.χ_rec]
  exact chiRec_eq_chi I l Z t.idl_ok 𝔞 h

end Chi

end GlobalTheory.Mem.R3.SelC

end
