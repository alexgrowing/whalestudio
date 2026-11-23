import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodRationalSchroedingerModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateUnitaryAdelicIsoMapHaarFundamentalDomaiStatement
import Development.AutomorphicArithmetic.DivisorFrames.ExistsSplitBasisConjLatticeOfSelfDualFrame
import Development.AutomorphicArithmetic.DivisorFrames.ExistsSplitBasisSkewLatticeOfFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HermitianSkewLattice

open GlobalTheory.TripleDarboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars)

private theorem selfDual_neg {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSelfDualC V Λ) : IsSelfDualC (sgn true V) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
  have e : ∑ i, ∑ j, star (x i) * (sgn true V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (x i) * (-V.gram i j) * y j = _
    ring
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩

private theorem herm_of_lat {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (S : HSp D)
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (hsd : IsSelfDualC S Λ₀)
    (s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D S τ) p q) :
    ∃ Λ bas, Spc.IsHerm D.sp.cm.sig B (Spc.mk ((-1 : D.host.E) • S.gram) Λ (fun w => -s (τf w)) bas) q p ∧
      ∀ y, y ∈ Λ ↔ star y ∈ Λ₀ := by
  have hlat := Formalism.L2.Col.brp_starLat_lattice _ _ hsd.1
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have eJ : ∀ w, ((-1 : D.host.E) • S.gram).map (B.emb w).1 = -((gramAt D S (τf w)).map star) := fun w => by
    ext a b; simp [gramAt, hB]
  refine ⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => GlobalTheory.TripleSpace.mem_starLat_iff_form S hsd y, fun w => ?_, hbas⟩,
    fun y => Iff.rfl⟩
  · show star (((-1 : D.host.E) • S.gram) b a) = ((-1 : D.host.E) • S.gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, GlobalTheory.TripleSpace.star_gram]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • S.gram).map (B.emb w).1) _ _
    rw [eJ]
    exact GlobalTheory.TripleSpace.hasSig_neg_of_hasSignature (hasSignature_map_conj (hsig _))
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • S.gram).map (B.emb w).1) _
    rw [eJ]
    exact GlobalTheory.TripleSpace.isCartan_neg_conj (hs _)

open scoped ComplexOrder in

private theorem skew_of_lat {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)) (hA : IsSelfDualC X Λ₀)
    (s : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D X τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D X τ) p q) :
    ∃ Λ bas, Spc.IsSkew D.sp.cm.sig B (Spc.mk (D.host.xi0 • (X.gramᵀ).submatrix e e) Λ
      (fun w => ((s (τf w)).submatrix e e).map conj) bas) p q ∧
      ∀ y, y ∈ Λ ↔ (fun k => y (e.symm k)) ∈ GlobalTheory.SkewLat.scLat D.host.AA Λ₀ := by
  let e' : Fin X.rank ⊕ Fin (zeroSp D).rank ≃ Fin k := (Equiv.sumEmpty (Fin X.rank) (Fin 0)).trans e.symm
  have hJ : D.host.xi0 • (X.gramᵀ).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram X (zeroSp D) e' :=
    congrArg (D.host.xi0 • ·) (blk_empty e _ _).symm
  have hZ := GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (zeroSp D)
  have hlat := GlobalTheory.SkewLat.isLattice_pairLat GlobalTheory.SkewLat.DualPair.AA_ne hA.1 hZ.1 e'
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have hsub : Subsingleton (Matrix (Fin (zeroSp D).rank) (Fin (zeroSp D).rank) ℂ) :=
    inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin 0) ℂ))
  have hsub' : Subsingleton (Fin (zeroSp D).rank → D.host.E) :=
    inferInstanceAs (Subsingleton (Fin 0 → D.host.E))
  refine ⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, hbas⟩, fun y => ?_⟩
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
  · refine GlobalTheory.SkewLat.mem_pairLat.trans ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [Subsingleton.elim (fun k => y (e' (.inr k))) 0]
    exact zero_mem _

private theorem ext_bas {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Base F E) {n : ℕ}
    (Q : ∀ v : B.P, GL (Fin n) (Fv F v) → Prop) (h : ∀ v, ∃ b, Q v b) :
    ∃ bas : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GL (Fin n) (Fv F v), ∀ v : B.P, Q v (bas v) := by
  choose b hb using h
  refine ⟨fun v => if hv : v ∈ B.P then b ⟨v, hv⟩ else 1, fun v => ?_⟩
  simp only [dif_pos v.2]
  exact hb v

end UpperTheory.HermitianSkewLattice

theorem UpperTheory.exists_geo_of_signature_rank_bounds :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW) (FA : Fr A) (FA' : Fr A') (FW : Fr WW)
        (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E) (p q : ℕ), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
        (∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) → X.rA.Is → X.rA'.Is → X.rW.Is →
        IsHaarFD A X.m X.fd → IsHaarFD A' X.m' X.fd' →
        GlobalTheory.ConstRatio.NegIdx A p → GlobalTheory.ConstRatio.NegIdx A' q → GlobalTheory.ConstRatio.NegIdx WW (p + q) →
        Even (A.rank + A'.rank) → A'.rank + 2 * (2 * (p + q) + 1) < A.rank → 2 * (p + q) + 1 < A'.rank →
        (∀ w, ((A.rank + A'.rank : ℕ) : ℤ) < Bs.mα w - Bs.mβ w) →
        ∃ Γ : Geo D.sp.cm.sig A.rank A'.rank, Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧ IsStageGeo ψ X FA FA' FW hr Bs Γ := by
  open GlobalTheory.TripleDarboux UpperTheory.HermitianSkewLattice in
  intro D ψ T A A' WW X FA FA' FW hr Bs p q hBs hψ hτ rA rA' rW hm hm' nA nA' nW hev h1 h2 hκ
  choose τf hemb using hτ
  have hneg : ∀ τ, gramAt D (sgn true A) τ = -gramAt D A τ := fun τ => by ext i j; simp [gramAt, neg_gram]
  obtain ⟨ΛV, basV, hV, lV⟩ := herm_of_lat Bs τf hemb (sgn true A) X.rA.Λ (selfDual_neg rA.1) (fun τ => sgnM true (FA.cart τ))
    (fun τ => isCartanInv_sgn true A τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv FA τ))
    (fun τ => by rw [hneg]; exact hasSignature_neg (nA τ))
  have eJ : (-1 : D.host.E) • (sgn true A).gram = (1 : D.host.E) • A.gram := by
    rw [neg_gram, neg_smul, one_smul, one_smul, neg_neg]
  have eθ : (fun w => -sgnM true (FA.cart (τf w))) = fun w => FA.cart (τf w) := funext fun w => neg_neg _
  rw [eJ, eθ] at hV
  obtain ⟨ΛV', basV', hV', lV'⟩ := herm_of_lat Bs τf hemb A' X.rA'.Λ rA'.1 FA'.cart
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv FA') nA'
  obtain ⟨ΛX, basX, hX, lX⟩ := skew_of_lat Bs τf hemb WW (finCongr hr) X.rW.Λ rW.1 FW.cart
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv FW) nW
  have e3 : WW.rank - (p + q) = A.rank + A'.rank - (p + q) := by rw [hr]
  rw [e3] at hX
  obtain ⟨bV, hbV⟩ := ext_bas Bs (n := A.rank) (fun v b => IsSplitBasis (Bs.τ v) ΛV b ∧
      (b⁻¹).1 = -(A.gram.map (Bs.τ v) * X.rA.β.1.map (evW (Bs.τ v)))ᵀ) fun v => by
    obtain ⟨b, -, hb, hb'⟩ := UpperTheory.exists_splitBasis_conj_lattice_of_selfDual_frame D A X.rA.Λ ΛV X.rA.β rA.1 rA.2.1 lV v (Bs.τ v)
    refine ⟨-b, hb, ?_⟩
    rw [inv_neg, Units.val_neg, hb']
  obtain ⟨bV', hbV'⟩ := ext_bas Bs (n := A'.rank) (fun v b => IsSplitBasis (Bs.τ v) ΛV' b ∧
      (b⁻¹).1 = (A'.gram.map (Bs.τ v) * X.rA'.β.1.map (evW (Bs.τ v)))ᵀ) fun v => by
    obtain ⟨b, hb, -, hb'⟩ := UpperTheory.exists_splitBasis_conj_lattice_of_selfDual_frame D A' X.rA'.Λ ΛV' X.rA'.β rA'.1 rA'.2.1 lV' v (Bs.τ v)
    exact ⟨b, hb, hb'⟩
  obtain ⟨bX, hbX⟩ := ext_bas Bs (n := A.rank + A'.rank) (fun v b => IsSplitBasis (Bs.τ v) ΛX b ∧
      (AUnit (Bs.τ v) → b.1 = (X.rW.β.1.map (evW (Bs.τ v))).submatrix (finCongr hr) (finCongr hr))) fun v => by
    by_cases hu : AUnit (Bs.τ v)
    · obtain ⟨c, hc, hc'⟩ := UpperTheory.exists_splitBasis_skewLattice_of_frame D _ _ (finCongr hr) X.rW.Λ ΛX X.rW.β rW.2.1 lX v (Bs.τ v) hu
      exact ⟨c, hc, fun _ => hc'⟩
    · exact ⟨basX v, hX.bas v, fun h => absurd h hu⟩
  let V : Spc D.host.F D.host.E A.rank := ⟨(1 : D.host.E) • A.gram, ΛV, fun w => FA.cart (τf w), bV⟩
  let V' : Spc D.host.F D.host.E A'.rank := ⟨(-1 : D.host.E) • A'.gram, ΛV', fun w => -FA'.cart (τf w), bV'⟩
  let Ws : Spc D.host.F D.host.E (A.rank + A'.rank) :=
    ⟨D.host.xi0 • (WW.gramᵀ).submatrix (finCongr hr) (finCongr hr), ΛX,
      fun w => ((FW.cart (τf w)).submatrix (finCongr hr) (finCongr hr)).map conj, bX⟩
  have gV : V.IsHerm D.sp.cm.sig Bs (A.rank - p) p :=
    ⟨hV.herm, hV.sig, hV.lat, hV.dual, hV.cartan, fun v => (hbV v).1⟩
  have gV' : V'.IsHerm D.sp.cm.sig Bs q (A'.rank - q) :=
    ⟨hV'.herm, hV'.sig, hV'.lat, hV'.dual, hV'.cartan, fun v => (hbV' v).1⟩
  have gW : Ws.IsSkew D.sp.cm.sig Bs (A.rank + A'.rank - (p + q)) (p + q) :=
    ⟨hX.skew, hX.sig, hX.lat, hX.dual, hX.cartan, fun v => (hbX v).1⟩
  obtain ⟨hμ1, hd1⟩ := GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_fundamentalDomain D A 1 (J := V.J) rfl one_ne_zero X.m X.fd hm
  obtain ⟨hμ2, hd2⟩ := GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_fundamentalDomain D A' (-1) (J := V'.J) rfl (neg_ne_zero.2 one_ne_zero) X.m' X.fd' hm'
  obtain ⟨M, hMμ, hMd, hM⟩ := GlobalTheory.T.exists_good_rational_schroedingerModel D Bs hBs V Ws _ _ _ _ gV gW _ _ hμ1 hd1
  obtain ⟨M', hMμ', hMd', hM'⟩ := GlobalTheory.T.exists_good_rational_schroedingerModel D Bs hBs V' Ws _ _ _ _ gV' gW _ _ hμ2 hd2
  refine ⟨⟨p, q, V, V', Ws, M, M'⟩, rfl, rfl, ⟨by omega, hev, hκ, ?_, h2, gV, gV', gW, hM, hM'⟩,
    ⟨⟨hBs, hψ, rfl, rfl, ⟨_, _, gV⟩, ⟨_, _, gW⟩, hM⟩, ⟨hBs, hψ, rfl, rfl, ⟨_, _, gV'⟩, ⟨_, _, gW⟩, hM'⟩,
      ⟨lV, lX⟩, ⟨lV', lX⟩, fun w => ⟨τf w, hemb w, (one_smul _ _).symm, rfl⟩,
      fun w => ⟨τf w, hemb w, (neg_one_smul _ _).symm, rfl⟩, rfl, rfl, hMμ, hMd, hMμ', hMd',
      fun v => (hbV v).2, fun v => (hbV' v).2, fun v => (hbX v).2⟩⟩
  obtain ⟨m, hm⟩ := hev
  show 2 * (p + q) + 1 < (A.rank - A'.rank) / 2
  omega
