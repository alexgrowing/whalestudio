import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DetSubMemOfConj
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTwistCharacterUnitsModSpecialIdealStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsometryAgreeing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOneStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistTie

open GlobalTheory.Member GlobalTheory.CharacterFunction

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem normOne_det (V : HSp D) (h : GA D V) : NormOne (D := D) (Matrix.GeneralLinearGroup.det (finHom V h)) := by
  have hb : ∀ z, barF D z = GlobalTheory.AdLat.sg (Af D.host.F) (cF D) z := fun _ => rfl
  unfold NormOne
  rw [hb, Matrix.GeneralLinearGroup.val_det_apply]
  exact (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V h).2.1

theorem det_eq_of_mulVec {E R : Type} [CommRing E] [CommRing R] (inc : E →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (δ : Matrix (Fin n) (Fin n) E) (h : ∀ v : Fin n → E, (G *ᵥ fun i => inc (v i)) = fun i => inc ((δ *ᵥ v) i)) :
    G.det = inc δ.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  have h2 : (fun i => inc ((Pi.single j 1 : Fin n → E) i)) = Pi.single j 1 := by
    funext b
    by_cases hb : b = j
    · subst hb
      simp
    · simp [hb]
  rw [h2, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h1
  exact h1

theorem det_rational (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : ∃ a : D.host.E,
    ((Matrix.GeneralLinearGroup.det (finHom V γ) : (AfE D)ˣ) : AfE D) = 1 ⊗ₜ a := by
  obtain ⟨δ, -, hδ, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  let inc : D.host.E →+* AfE D := (Algebra.TensorProduct.includeRight (R := D.host.F)).toRingHom
  refine ⟨δ.1.det, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact det_eq_of_mulVec inc (finHom V γ).1 δ.1 hδ

theorem gLat_one (V : HSp D) : gLat V 1 = latHat V := by
  unfold gLat
  rw [map_one, Units.val_one]
  exact (Set.image_congr fun z _ => Matrix.one_mulVec z).trans (Set.image_id _)

theorem sub_eq_nsmul_of_split {L A : Type} [AddCommGroup L] [AddCommGroup A] (j : L → A) (u : A →+ A)
    (hadd : ∀ x y, j (x + y) = j x + j y) (hsm : ∀ (n : ℕ) x, j (n • x) = n • j x) {M p : ℕ} {a b e z : L} {w : A}
    (ha : a = b + M • e) (hw : u (j b) - j (b + M • z) = (M * p) • w) :
    j a - u (j a) = M • (j e - u (j e) - j z - p • w) := by
  rw [hadd, hsm, mul_smul, sub_eq_iff_eq_add] at hw
  rw [ha, hadd, hsm, map_add, map_nsmul, hw]
  simp only [smul_sub]
  abel

set_option maxHeartbeats 1000000 in

theorem congOne_det (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LatEmb V io)
    {l l₂ : Level H} {p : ℕ} {I : Ideal (𝓞 D.host.E)} (hM : l₂.M = l.M * p) (hcop : p.Coprime l.M)
    (hMb : l₂.Mb = l.Mb * I) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La)
    (hs : ∀ a, s a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) (u : GA D V) (hu : gLat V u = latHat V)
    (h : ∀ a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      (finHom V u).1.mulVec (finVec V (io a)) - finVec V (io (s a)) = l₂.M • w) :
    CongOne l.M (Matrix.GeneralLinearGroup.det (finHom V u)) := by
  have hκ : latGHat V u = latGHat V 1 := by unfold latGHat; rw [hu, gLat_one]
  have hlat : latG V 1 = latG V u := by unfold latG; rw [hu, gLat_one]
  have hmem : ∀ a, finVec V (io a) ∈ latGHat V 1 := fun a =>
    ((GlobalTheory.MarkCoset.latG_spec D V 1).1 _).1 (hio.2 ▸ LinearMap.mem_range_self io a)
  have hadd : ∀ x y, finVec V (x + y) = finVec V x + finVec V y := GlobalTheory.AdLat.cap_fv_add D.host.F
  have hsm : ∀ (n : ℕ) x, finVec V (n • x) = n • finVec V x := GlobalTheory.AdLat.cap_fv_nsmul D.host.F
  have hpI : (p : 𝓞 D.host.E) ∈ I.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) (natCast_mem_half hM hMb)
    rwa [map_natCast] at this
  obtain ⟨α, β, hαβ⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hc : FinCong V l.M (1⁻¹ * u) := by
    refine GlobalTheory.CharRead.finCong_of_marks l V io hio 1 u hlat (fun a => finVec V (io a)) (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, sub_self]⟩) fun a ha => ?_
    have hb : α • a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := zsmul_mem ha α
    have hsplit : a = p • (α • a) + l.M • (β • a) := by
      rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, mul_comm _ α, mul_comm _ β, hαβ, one_smul]
    generalize α • a = b at hb hsplit
    generalize β • a = e at hsplit
    have hb₂ : p • b ∈ Mfr l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
      rw [Mfr, hMb, Ideal.map_mul, mul_comm, Submodule.mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]
      exact Submodule.smul_mem_smul hpI hb
    obtain ⟨w, hw, ew⟩ := h _ hb₂
    obtain ⟨z, hz⟩ := GlobalTheory.ShortMove.exists_eq_nsmul l (hs (p • b))
      (sub_mem (GlobalTheory.LevStab.map_mem_smul_top _ s (nsmul_mem hb p)) (nsmul_mem hb p))
    have hue : (finHom V u).1 *ᵥ finVec V (io e) ∈ latGHat V 1 :=
      hκ ▸ ((GlobalTheory.MarkCoset.latG_spec D V u).2 _).2 ⟨_, hmem e, rfl⟩
    refine ⟨finVec V (io e) - (finHom V u).1 *ᵥ finVec V (io e) - finVec V (io z) - p • w,
      hκ ▸ sub_mem (sub_mem (sub_mem (hmem e) hue) (hmem z)) (nsmul_mem hw p), ?_⟩
    rw [sub_eq_iff_eq_add'.1 hz, hM] at ew
    exact sub_eq_nsmul_of_split (fun x => finVec V (io x)) (finHom V u).1.mulVecLin.toAddMonoidHom
      (fun x y => by rw [map_add, hadd]) (fun n x => by rw [map_nsmul, hsm]) hsplit ew
  rw [inv_one, one_mul] at hc
  obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨w, hw, e⟩ := GlobalTheory.CharRead.det_cong_one D.host.F (latC V) k3 k4 l.M (by have := l.three_le; omega)
    (finHom V u).1 (by rw [← k1]; exact hc)
  exact ⟨w, GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers D ▸ hw, e⟩

theorem exists_basis_lift {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] (I J : Ideal R) (hIJ : IsCoprime I J)
    {r : ℕ} (e : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (Fin r → R ⧸ I)) :
    ∃ v : Fin r → L, (∀ j, v j ∈ (J • ⊤ : Submodule R L)) ∧
      (∀ j, (Submodule.Quotient.mk (v j) : L ⧸ (I • ⊤ : Submodule R L)) = e.symm (Pi.single j 1)) ∧
      (⊤ : Submodule R L) ≤ Submodule.span R (Set.range v) ⊔ I • ⊤ := by
  obtain ⟨a, ha, c, hc, hac⟩ := Ideal.isCoprime_iff_exists.1 hIJ
  choose x hx using fun j => Submodule.Quotient.mk_surjective (I • ⊤ : Submodule R L) (e.symm (Pi.single j 1))
  have hv : ∀ j, (Submodule.Quotient.mk (c • x j) : L ⧸ (I • ⊤ : Submodule R L)) = e.symm (Pi.single j 1) := fun j => by
    rw [← hx, eq_comm, Submodule.Quotient.eq, eq_sub_of_add_eq' hac, sub_smul, one_smul, sub_sub_cancel]
    exact Submodule.smul_mem_smul ha trivial
  refine ⟨fun j => c • x j, fun j => Submodule.smul_mem_smul hc trivial, hv, fun y _ => ?_⟩
  choose co hco using fun i => Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk y) i)
  have h0 : y - ∑ i, co i • c • x i ∈ (I • ⊤ : Submodule R L) := by
    rw [← Submodule.Quotient.eq]
    apply e.injective
    rw [← Submodule.mkQ_apply _ (∑ i, _), map_sum, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul _ c, hv, e.apply_symm_apply]
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one, ← hco]
      rfl
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne hb.symm, smul_zero]
    · simp
  rw [← add_sub_cancel (∑ i, co i • c • x i) y]
  exact Submodule.add_mem_sup
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) h0

set_option maxHeartbeats 1000000 in

theorem exists_psiTie_of_values (V : HSp D) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ}
    (d : DeltaDat Xo c n) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hι : IotaOK Dw V io) (hpq : 1 ≤ Dw.p + Dw.q) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (X₀ : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (hX₀ : ModelW V hr X₀)
    (hX₀' : X₀.p0 = Dw.q ∧ ∀ τ : D.host.E →+* ℂ, τ ∈ X₀.Ψ ↔ τ (H.rt : D.host.E) = H.rt0) (hx₀ : IsOrthogonalFrame X₀ x₀)
    (hlM : l.M = D.host.g 0 * D.host.g 1) (hFO : FO D ≤ c.F) (hp : d.pd.Prime) (hd : d.IsLev) (hA₂ : d.l₂.A = 1)
    (xi : (AfE D)ˣ →* ℂˣ) (hxi : XiOK D d.pd xi) (U₂ : _) (dict₂ : _)
    (hv : CXiVal V hr c.F.val.toRingHom (Tup := Unit) (fun _ => d) U₂ dict₂ io x₀ fun _ => xi) :
    ∃ ψ, ψ ≠ 1 ∧ d.PsiTie ψ := by
  subst hr
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hv
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv ()
  obtain ⟨-, hM, hcop, hMb, hI, -, -, hsec, -⟩ := hd
  obtain ⟨m', hm', hfin⟩ := hxi.fin
  have hbar : (barE D : 𝓞 D.host.E →+* 𝓞 D.host.E) = (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) := RingHom.ext fun a => by
    apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
    show ((barE D a : 𝓞 D.host.E) : D.host.E) = ((H.bar a : 𝓞 D.host.E) : D.host.E)
    rw [H.bar_eq a]
    rfl
  have hprod := GlobalTheory.DatumInverseCharacter.half_prod hM hMb
  obtain ⟨χ, hχ1, hχ⟩ := GlobalTheory.T.exists_twistCharacter_units_mod_specialIdeal D d.pd d.I xi hp (hlM ▸ hcop) (hbar ▸ hprod) (hbar ▸ hI) hxi
  have hpI : (d.pd : 𝓞 D.host.E) ∈ d.I := natCast_mem_half hM hMb
  have hI0 : d.I ≠ ⊥ := fun e => hp.ne_zero (by rw [e, Ideal.mem_bot] at hpI; exact_mod_cast hpI)
  haveI : Finite (𝓞 D.host.E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I V.rank (Dw.rank.trans hU.1.symm)
  obtain ⟨δ, hδs, hδ⟩ := exists_det_hom d.I (hU.1 ▸ hpq) e
  have hItop : d.I ≠ ⊤ := fun hT => by
    haveI := Ideal.Quotient.subsingleton_iff.2 hT
    exact hχ1 (MonoidHom.ext fun u => by rw [Subsingleton.elim u 1, map_one, map_one])
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hMl : ∀ l : Level H, (l.M : 𝓞 D.host.E) ∈ l.Mb := fun l => by
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  have hIJ : IsCoprime d.I (Mfr d.l₂) := by
    rw [Mfr, hMb, Ideal.map_mul]
    refine IsCoprime.mul_right ?_ (Ideal.isCoprime_iff_sup_eq.2 hI)
    obtain ⟨α, β, hαβ⟩ := Nat.Coprime.cast (R := 𝓞 D.host.E) hcop
    have h1 := Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) (hMl l)
    rw [map_natCast] at h1
    exact Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.mul_mem_left _ α hpI, _, Ideal.mul_mem_left _ β h1, hαβ⟩
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_basis_lift d.I (Mfr d.l₂) hIJ e
  let inc : (FO D)ˣ →* c.Fˣ := Units.map (IntermediateField.inclusion hFO).toRingHom.toMonoidHom
  refine ⟨inc.comp (χ.comp δ), fun h => hχ1 (MonoidHom.ext fun u => ?_), fun k g ρ hg _ hρ hk K _ _ _ y y' hy => ?_⟩
  · obtain ⟨k, rfl⟩ := hδs u
    have := congrArg (fun z : c.Fˣ => ((z : c.F) : ℂ)) (DFunLike.congr_fun h k)
    exact Units.ext (Subtype.ext this)
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  obtain ⟨u, -, hu, hlift⟩ := GlobalTheory.HalfLift.exists_unitary_inducing D H Dw d.l₂ V io hι (g.f d.l₂.M) g' fun a => by
    obtain ⟨⟨b, hb⟩, b', hb'⟩ := hg' a
    exact ⟨hb ▸ nsmul_mem_smul_top (hMl _) b, hb' ▸ nsmul_mem_smul_top (hMl _) b'⟩
  have hlow : ∀ a, g.f d.l₂.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := fun a => by
    obtain ⟨w, hw⟩ := g.tower l.M d.pd hM0 hp.pos a
    rw [← hM] at hw
    have := add_mem (hw ▸ nsmul_mem_smul_top (hMl l) w) (hg.2.1 a)
    rwa [sub_add_sub_cancel] at this
  have hcong := congOne_det V io hι.emb hM hcop hMb _ hlow u hu hlift
  have hrange : (latG V 1 : Set (Fin V.rank → D.host.E)) = Set.range io := by
    rw [← hι.emb.2, LinearMap.coe_range]
  obtain ⟨a, ha₁, ha₂⟩ := det_sub_mem_hat D.host.F io (hrange ▸ (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.1) d.I hItop v hv₃ (g.f d.l₂.M)
    d.l₂.M (by rw [hM, Nat.cast_mul]; exact d.I.mul_mem_left _ hpI) (finHom V u).1 (by
      obtain ⟨w, hw, ew⟩ := hcong
      rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
      rw [← Matrix.GeneralLinearGroup.val_det_apply, sub_eq_iff_eq_add.1 ew]
      exact add_mem (nsmul_mem hw _) (GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers D ▸ (intRing D.host.F).one_mem))
    (fun j => by
      rw [← hrange, ← (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1]
      exact hlift _ (hv₁ j))
  have hdet := hδ k a fun j => by
    rw [← hv₂, ← hk, (Submodule.Quotient.eq _).2 (ha₁ j), ← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hv₂]
  have hval' := hχ _ a.det (δ k) (normOne_det V u) (hlM ▸ hcong) hdet ha₂
  refine value_ratio V (U₂ ()) (dict₂ ()) io e₀ F ik φ th x₀ (RingHom.ext fun _ => rfl) hA₂ hpq hU hW hD hι hth
    (fun k τ hτ => ?_) d.cδ hsec c0 xi (m * m') (Nat.mul_pos hm hm') (by rw [pow_mul, hc0, one_pow])
    (fun h => by rw [mul_comm, pow_mul, hfin _ (normOne_det V h), one_pow]) hval (fun γ hγ => ?_) g ρ hρ u
    (by unfold latGHat; rw [hu, gLat_one]) (fun b hb => ?_) _ hval'.symm K y y' hy
  · rw [(hW k).1, ← hX₀.1, (hU.2.1 k).1, ← hX₀'.1]
    exact hx₀ τ ((hX₀'.2 τ).2 (((hU.2.1 k).2 τ).1 hτ))
  · obtain ⟨b, hb⟩ := det_rational V hγ
    exact hxi.rat _ b hb (normOne_det V γ)
  · obtain ⟨w, hw, ew⟩ := hlift b hb
    exact ⟨w, hw, sub_eq_iff_eq_add'.1 ew⟩

theorem exists_psiTie_of_xiAt : ∀ (D : D7) (J : CoreJ D), LawsJ J → ∀ j, InR D j → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)) (d : DeltaDat (J.Q.Xo j) J.Q.c 0) (xi : (AfE D)ˣ →* ℂˣ), p.Prime → CoverOK d p I → FnAlgClosed d.Xo₂ d.c₂ → XiOK D p xi → XiAt J j d xi → ∃ ψ, ψ ≠ 1 ∧ d.PsiTie ψ := by
  rintro D J hJ j hj p I d xi hp ⟨rfl, -, hd, hA₂, -⟩ - hxi ⟨hr, U₂, dict₂, hv⟩
  have hσ := J.toCore.good_σ₀
  obtain ⟨_, _, _, _, _, _, _, hL, hI, -⟩ := hJ.adPin j hj J.σ₀ hσ
  obtain ⟨_, hW⟩ := hJ.modelW j hj J.σ₀ hσ
  have k := (J.dict j J.σ₀ 1).1
  exact exists_psiTie_of_values (J.V j J.σ₀) d hr _
    ⟨hJ.pins.1.2.1, hJ.pins.1.2.2.1, hL, GlobalTheory.ShortMove.formPlus_of hJ.pins hj (hJ.spaceW j hj _ hσ) hL hI⟩
    (GlobalTheory.ShortMove.rank_eq hJ.pins hj) _ _ (hW k) ((hJ.unf j hj _ hσ).2.1 k) (hJ.familyUniformisationBasePointOrthogonal j hj _ hσ k) hJ.pins.2.1.1
    (GlobalTheory.FinalJoin.FieldAlg.recordField_le_of_pinField J.Q hJ.pins.2.2.1) hp hd hA₂ xi hxi U₂ dict₂ hv

end GlobalTheory.TwistTie
