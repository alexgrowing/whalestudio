import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.BotMatch

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)
open GlobalTheory.TripleDarboux
open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat)

theorem exists_isHerm_lat {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (hsd : IsSelfDualC S Λ) (s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D S τ) p q) :
    ∃ bas, Spc.IsHerm D.sp.cm.sig B (Spc.mk ((-1 : D.host.E) • S.gram) (conjSub Λ) (fun w => -s (τf w)) bas) q p := by
  have hlat := GlobalTheory.TripleSpaceW.conjSub_isLattice hsd.1
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have eJ : ∀ w, ((-1 : D.host.E) • S.gram).map (B.emb w).1 = -((gramAt D S (τf w)).map star) := fun w => by
    ext a b; simp [gramAt, hB]
  refine ⟨bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => GlobalTheory.TripleSpace.mem_starLat_iff_form S hsd y, fun w => ?_, hbas⟩⟩
  · show star (((-1 : D.host.E) • S.gram) b a) = ((-1 : D.host.E) • S.gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, GlobalTheory.TripleSpace.star_gram]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • S.gram).map (B.emb w).1) _ _
    rw [eJ]
    exact GlobalTheory.TripleSpace.hasSig_neg_of_hasSignature (hasSignature_map_conj (hsig _))
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • S.gram).map (B.emb w).1) _
    rw [eJ]
    exact GlobalTheory.TripleSpace.isCartan_neg_conj (hs _)

open scoped ComplexOrder in

theorem exists_isSkew_lat {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (X : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E))
    (hA : IsSelfDualC X Λ) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (s : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D X τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D X τ) p q) :
    ∃ (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (bas : _),
      (∀ y : Fin k → D.host.E, (fun a => y (e.symm a)) ∈ scLat D.host.AA Λ → y ∈ L) ∧
      Spc.IsSkew D.sp.cm.sig B (Spc.mk (D.host.xi0 • (X.gramᵀ).submatrix e e) L
      (fun w => ((s (τf w)).submatrix e e).map conj) bas) p q := by
  let e' : Fin X.rank ⊕ Fin (zeroSp D).rank ≃ Fin k := (Equiv.sumEmpty (Fin X.rank) (Fin 0)).trans e.symm
  have hJ : D.host.xi0 • (X.gramᵀ).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram X (zeroSp D) e' :=
    congrArg (D.host.xi0 • ·) (blk_empty e _ _).symm
  have hZ := GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (zeroSp D)
  have hlat := GlobalTheory.SkewLat.isLattice_pairLat GlobalTheory.SkewLat.DualPair.AA_ne hA.1 hZ.1 e'
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have hsub : Subsingleton (Matrix (Fin (zeroSp D).rank) (Fin (zeroSp D).rank) ℂ) :=
    inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin 0) ℂ))
  refine ⟨_, bas, fun y hy => ?_, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, hbas⟩⟩
  · refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨hy, ?_⟩
    have : (fun k => y (e' (.inr k))) = 0 := funext fun k => Fin.elim0 k
    rw [this]
    exact zero_mem _
  · show star (D.host.xi0 * X.gram (e a) (e b)) = -(D.host.xi0 * X.gram (e b) (e a))
    rw [star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, GlobalTheory.TripleSpace.star_gram, neg_mul]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1) _ _
    rw [hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w)]
    have h0 : Formalism.UG.HasSignature (gramAt D (zeroSp D) (τf w)) 0 0 :=
      ⟨(Equiv.sumEmpty (Fin 0) (Fin 0)).symm, 1, by ext (a | a) <;> exact a.elim0⟩
    exact GlobalTheory.SkewLat.hasSig_blk e' _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hsig _) h0
  · show y ∈ _ ↔ ∀ x ∈ _, ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E
      (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (D.host.xi0 • (X.gramᵀ).submatrix e e) y x))
    rw [hJ]
    exact GlobalTheory.SkewLat.dual_pairLat (fun c hc => GlobalTheory.SkewLat.star_mem_AA hc) _ _ hA hZ e' y
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1)
      (((s (τf w)).submatrix e e).map conj)
    rw [hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w), ← blk_empty e (s (τf w)) 1]
    have h0 : IsCartanInv (gramAt D (zeroSp D) (τf w)) 1 :=
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, by
        rw [Subsingleton.elim (gramAt D (zeroSp D) (τf w) * 1) 1]; exact Matrix.PosDef.one⟩
    exact GlobalTheory.SkewLat.isCartan_blk e' _ _ _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hs _) h0

theorem exists_reading_lat {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X) {α β : (AE D)ˣ →* Circle} (h : IsTriple W W₁ X α β)
    {ωA : WRep W X} {ωB : WRep W₁ X} (hA : IsWeil ψ true W X β (β / α) ωA) (hB : IsWeil ψ false W₁ X α (α / β) ωB)
    {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} {ΛW₁ : Submodule (𝓞 D.host.E) (Fin W₁.rank → D.host.E)}
    {ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)} (sW : IsSelfDualC (sgn true W) ΛW) (sW₁ : IsSelfDualC W₁ ΛW₁)
    (sX : IsSelfDualC X ΛX) (Pw : Finset (Pl D.host.E))
    (hτ : ∀ v : Pl D.host.F, (∃ w ∈ Pw, w.under (𝓞 D.host.F) = v) → ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∀ w ∈ Pw, w.under (𝓞 D.host.F) = v → GlobalTheory.AdelicU.splitPrime τ = w)
    (hram : ∀ w ∈ Pw, ¬ GlobalTheory.LFun.UnrAt (α / β) w)
    (hunr : ∀ w : Pl D.host.E, (∀ w' ∈ Pw, w'.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) →
      GlobalTheory.LFun.UnrAt α w ∧ GlobalTheory.LFun.UnrAt β w) :
    ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (hr : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β (finCongr h.rank.symm) Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA (finCongr h.rank.symm) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hr.JW)
        (GlobalTheory.TripleRead.toUX X (finCongr h.rank.symm) hr.JX) ∧
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB (finCongr h.rank.symm) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hr.JW₁)
        (GlobalTheory.TripleRead.toUX X (finCongr h.rank.symm) hr.JX) ∧
      Γ.V.L = conjSub ΛW ∧ Γ.V'.L = conjSub ΛW₁ ∧
      (∀ y : Fin (W.rank + W₁.rank) → D.host.E,
        (fun a => y ((finCongr h.rank.symm).symm a)) ∈ scLat D.host.AA ΛX → y ∈ Γ.W.L) ∧
      Xc.T = Bs.P ∧ ∀ w, w ∈ Pw ↔ ∃ v : Bs.P, GlobalTheory.AdelicU.splitPrime (Bs.τ v) = w := by
  classical
  let e : Fin (W.rank + W₁.rank) ≃ Fin X.rank := finCongr h.rank.symm
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  choose a b ha hb hab using h.gap
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_ram_set h
  have hdiv : ∀ w, GlobalTheory.LFun.UnrAt α w ∧ GlobalTheory.LFun.UnrAt β w → GlobalTheory.LFun.UnrAt (α / β) w := fun w hw => by
    rw [div_eq_mul_inv]; exact hw.1.mul hw.2.inv
  have hTP : ∀ v ∈ T, ∃ w ∈ Pw, w.under (𝓞 D.host.F) = v := fun v hv => by
    by_contra hc
    push Not at hc
    obtain ⟨τ₀⟩ := (hT1 v hv).1
    have hu := GlobalTheory.AdelicU.splitPrime_under τ₀
    exact hT2 _ (hu.symm ▸ hv) (hdiv _ (hunr _ fun w' hw' => hu.symm ▸ hc w' hw'))
  have hPT : ∀ w ∈ Pw, w.under (𝓞 D.host.F) ∈ T := fun w hw => by
    by_contra hc
    exact hram w hw (hdiv w (hT3 w hc))
  choose τP hτP using fun v : T => hτ v.1 (hTP v.1 v.2)
  obtain ⟨v₁, hv₁, hv₁s, ⟨τ₁⟩⟩ := exists_good_place D T
  let Bs : Base D.host.F D.host.E := ⟨ψ, fun w => ⟨_, hτf w⟩, mα, mβ, T, τP, v₁, τ₁⟩
  have hBs : Bs.IsGood D.sp.cm.sig := base_isGood Bs hψ fun v hv => (hT1 v hv).2
  have hemb : ∀ w x, (Bs.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨p, q, hsig, hn1, hn2⟩ := h.sig
  have hneg : ∀ τ, gramAt D (sgn true W) τ = -gramAt D W τ := fun τ => by ext i j; simp [gramAt, neg_gram]
  obtain ⟨basV, hV⟩ := exists_isHerm_lat Bs τf hemb (sgn true W) ΛW sW (fun τ => sgnM true (A.cart τ))
    (fun τ => isCartanInv_sgn true W τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ))
    (fun τ => by rw [hneg]; exact hasSignature_neg (hsig τ).1)
  have eJ : (-1 : D.host.E) • (sgn true W).gram = (1 : D.host.E) • W.gram := by
    rw [neg_gram, neg_smul, one_smul, one_smul, neg_neg]
  have eθ : (fun w => -sgnM true (A.cart (τf w))) = fun w => A.cart (τf w) := funext fun w => neg_neg _
  rw [eJ, eθ] at hV
  obtain ⟨basV', hV'⟩ := exists_isHerm_lat Bs τf hemb W₁ ΛW₁ sW₁ A₁.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A₁)
    fun τ => (hsig τ).2.1
  obtain ⟨LX, basX, hLX, hX⟩ := exists_isSkew_lat Bs τf hemb X ΛX sX e B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
    fun τ => (hsig τ).2.2
  have e3 : X.rank - (p + q) = W.rank + W₁.rank - (p + q) := by rw [h.rank]
  rw [e3] at hX
  obtain ⟨Mo, hMo⟩ := exists_model Bs hBs W _ _ hV hX 1 one_ne_zero rfl
  obtain ⟨Mo', hMo'⟩ := exists_model Bs hBs W₁ _ _ hV' hX (-1) (neg_ne_zero.2 one_ne_zero) rfl
  obtain ⟨om, hom, htr⟩ := exists_weil Bs hBs true W X e _ _ hV hX 1 rfl (by rw [neg_gram, one_smul, neg_neg]) rfl Mo hMo hA
  obtain ⟨om', hom', htr'⟩ := exists_weil Bs hBs false W₁ X e _ _ hV' hX (-1) rfl (neg_one_smul _ _) rfl Mo' hMo' hB
  have hr := h.rank
  have hev := h.even
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have hTe : (⟨α, β, T, ∅⟩ : Chars D.host.F D.host.E).T = T := by simp [Chars.T]
  refine ⟨Bs, ⟨p, q, _, _, _, Mo, Mo'⟩, ⟨α, β, T, ∅⟩, om, om',
    ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, ⟨hBs, ?_, ?_, hom, hom'⟩, htr, htr',
    rfl, rfl, hLX, hTe, fun w => ⟨fun hw => ⟨⟨_, hPT w hw⟩, hτP _ w hw rfl⟩, ?_⟩⟩
  · refine ⟨by omega, hr ▸ hev, fun w => ?_, ?_, hn2, hV, hV', hX, hMo, hMo'⟩
    · have h1 := eα w
      have h3 := eβ w
      have h4 := hab (τf w)
      rw [hr] at h4
      have : (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
        push_cast at h4 ⊢
        rw [h1, h3]
        linarith
      exact_mod_cast this
    · obtain ⟨m, hm⟩ := hev
      show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2
      omega
  · refine ⟨h.hecA, h.hecB, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resA),
      GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resB), hα, hβ, Finset.disjoint_empty_right _,
      hTe.le, fun w hw => hT2 w (hTe ▸ hw), fun w hw => (hT3 w fun h0 => hw ?_).1, fun w hw => (hT3 w fun h0 => hw ?_).2,
      ⟨hTe.symm ▸ hv₁, hv₁s⟩⟩
    · rw [hTe]; exact h0
    · rw [hTe]; exact h0
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hTP v.1 v.2
    exact (hτP v w hw hwv).symm ▸ hw

end GlobalTheory.BotMatch

end
