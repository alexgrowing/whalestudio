import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleAdm
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual
section Algebra
variable {g : ℕ} [Fact g.Prime]
end Algebra
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar Formalism.L2.Host
variable {D : D7}
section Row
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}
end Row
section Comparison₂
variable {Y : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : Y.Tw} {b : Bool}
variable {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}
theorem exists_kappa_of_isTripleWith (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) {s : Y.Sig i} {ρ : Reading Y i (Y.side i s)}
    (hχ : IsChars C art ρ) {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (Y.l i))}
    {ν : GalE D →* (Y.O0 i)ˣ} {w : D.what₂.places.Pl} {red : Zbar (Y.l i) →+* FbAt D w}
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : ∃ κ, IsRowOfTriple Y i s σ w κ := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hl := h.induces.resChar
  obtain ⟨κ, hκ⟩ := exists_residue_lift ρ (red.comp (toZ ρ)) (by rw [← hl]; exact CharP.cast_eq_zero _ _)
  refine ⟨κ, h.good, h.occurs, hl, fun x => ?_,
    ⟨(Units.map (red.comp (toZ ρ)).toMonoidHom).comp ν, fun v hv A hA t ht => ?_, fun g => ?_⟩, fun k hk v => ?_⟩
  · obtain ⟨-, -, hint, -⟩ := GlobalTheory.CoefEmbed.embedding_closed_integral _ _ (Y.twistBaseCoefficientRing_isAdic i) ρ.κ ρ.κ_alg
    have e : ∀ y : ↥D.LL0, ρ.ι.symm (D.what₂.embLL (y : D.what₂.LL)) = ρ.κ (GlobalTheory.Triple.embSide Y i (Y.side i s) y) :=
      fun y => by rw [RingEquiv.symm_apply_eq, ρ.read]; rfl
    have h1 : 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔
        ‖ρ.κ (GlobalTheory.Triple.embSide Y i (Y.side i s) (x : ↥D.LL0))‖ < 1 := by
      rw [← e]
      generalize ((x : ↥D.LL0) : D.what₂.LL) = y
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      have h2 := h.induces y⁻¹
      have h3 : 0 < ‖ρ.ι.symm (D.what₂.embLL y)‖ := by simpa using hy
      rw [map_inv₀ D.what₂.embLL, map_inv₀ ρ.ι.symm, norm_inv, inv_le_one₀ h3] at h2
      rw [← not_le, ← not_le, ← h2, not_iff_not, AddValuation.map_inv]
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 ((D.what₂.places.val w).ne_top_iff.2 hy)
      rw [← hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_zero, WithTop.coe_le_coe,
        WithTop.coe_le_coe, neg_nonneg]
    rw [h1]
    refine ⟨?_, fun h2 => ?_⟩
    · rintro ⟨y, hy, e1⟩
      rw [GlobalTheory.Triple.embSide, ← e1]
      exact (mem_maximalIdeal_iff ρ y).1 hy
    · obtain ⟨y, hy⟩ := hint _ h2.le
      exact ⟨y, (mem_maximalIdeal_iff ρ y).2 (by rw [← hy] at h2; exact h2), hy⟩
  · obtain ⟨n, hn⟩ := h.shift
    rw [MonoidHom.comp_apply, (hn.unr_iff ha (Or.inl hv) hA).2 (GlobalTheory.Triple.shiftChar_unr C v) t ht, map_one]
  · obtain ⟨p, h1, h2⟩ := h.residual.charpoly g
    let M : Matrix (Fin D.R.r) (Fin D.R.r) (Y.O0 i) := (((ν g)⁻¹ : (Y.O0 i)ˣ) : Y.O0 i) •
      ((Y.rhoS i s g : GL (Fin D.R.r) (Y.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (Y.O0 i))
    have e1 : (M.map (toZ ρ)).map (Zbar (Y.l i)).subtype = (r g : GL (Fin D.R.r) (Qbar (Y.l i))) := by
      ext x y
      have := congrFun (congrFun (h.rho g) x) y
      change toQ ρ.κ (_ * _) = _
      rw [map_mul]
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [this, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    have e2 : p = (M.map (toZ ρ)).charpoly :=
      Polynomial.map_injective (Zbar (Y.l i)).subtype Subtype.val_injective (by rw [h1, ← Matrix.charpoly_map, e1])
    rw [e2, ← Matrix.charpoly_map] at h2
    rw [← charpoly_smul_congr _ h2]
    congr 1
    ext x y
    change κ (IsLocalRing.residue _ _) = red (toZ ρ (ν g : (Y.O0 i)ˣ)) * red (toZ ρ (_ * _))
    rw [hκ, ← map_mul, ← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rfl
  · obtain ⟨u, hu, e⟩ := hχ.tame (jIdx s) k hk.symm v
    refine ⟨u, hu, (hκ _).trans (h.residual.teich k hk.symm v _ (toFb_ne_zero k u) _ ?_)⟩
    rw [← e, GlobalTheory.Triple.jIdx_add_one, Reading.toC_apply, RingEquiv.symm_apply_apply]
    rfl
variable {Z : NExp D.R D.host D.what₂ D.LL0 D.nd Y}
theorem blockCharConj_of_isTripleOf (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Z) : BlockCharConj Y := by
  obtain ⟨C, art, h⟩ := h
  intro i hi j b h1 h2 k hk v hv A hA t ht t' ht'
  obtain ⟨ρ, hχ, -⟩ := h.evidence i hi b
  obtain ⟨j, rfl⟩ : ∃ j' : Fin D.R.m, j = j'.1 + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨n, hn⟩ := hχ.chi j
  obtain ⟨n0, h0⟩ := exists_isAlgPos_mu0 (hframe C) GlobalTheory.Triple.eExp_int j
  obtain ⟨r, hr, hL⟩ := h.artin.exists_isLAdicOf ρ.ι (isAlgPos_mul h0 (del_alg (hframe C) (Y.l i)))
  have hanti : AntiHom Y.cc r := antiHom_of_isLAdicOf h.artin hr hL
    (((hframe C).isMu0 j).triv.mul (inertialOrderFifteenChar_auxiliaryPrime_spec (hframe C) (l := Y.l i)).2.2.2.2.triv)
  have key : ∀ v, v ∉ placesOver D.host.E (Y.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ t ∈ Ine (F := D.host.E) A, inQ ρ.κ (Y.chi1 i (j.1 + 1) b) t = r t := fun v hv A hA t ht => by
    obtain ⟨x, hx, e⟩ := exists_unit h.artin hA ht
    have e1 := hn.loc (Or.inl hv) e
    rw [GlobalTheory.Triple.blockChar, block_loc (C.isEta.unr v) hx] at e1
    apply Units.ext
    rw [hL.loc_away (Or.inl hv) x t e, inQ_val, RingEquiv.eq_symm_apply]
    exact e1
  have hvl : v ∉ placesOver D.host.E (Y.l i) := notMem_of_ne (D.host.g_prime k) (Y.lPrime i).out hk hv
  obtain ⟨bar, -, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  obtain rfl : t' = cConj Y t := AlgEquiv.ext ht'
  rw [← map_inv]
  refine inQ_inj ρ.κ ?_
  rw [map_inv, key v hvl A hA t ht, key (bar v) (fun hm => hvl (mem_placesOver_conj (TwistDet.isConjPl_symm (hbar v).1) hm)) _
    (isPlaceOver_moveVal_cc Y (hbar v).1 hA) _ (cConj_mem_ine Y ht), hanti t _ ht']
theorem gen_adm2_of_isTripleOf (hT : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Z) (hW : WildOne D) : BlochKatoReduction.Gen.adm2 Y := by
  intro i hi s
  have hχ := _root_.GlobalTheory.TripleAdm.blockCharConj_of_isTripleOf hT
  obtain ⟨C, art, h⟩ := hT
  obtain ⟨ρ, h1, σ, π, r, ν, w, red, h2⟩ := h.triple hi s
  obtain ⟨κ, h3⟩ := _root_.GlobalTheory.TripleAdm.exists_kappa_of_isTripleWith h.artin h1 h2
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hl := h2.induces.resChar
  obtain ⟨hirr, hrow⟩ := _root_.GlobalTheory.TripleAdm.irredOn_rbar_and_inertia_of_residual Y hW h2.good h2.param hl h2.gal h2.residual
  refine admissible_at_of_irreducible_tame h3 hirr fun k hk v hv A hA => ?_
  refine tameOff_all Y (fun e => hk (e.symm.trans hl)) (D.ntypes.rbar_open σ w) (fun v => (hrow k hk.symm v).1)
    (fun v t ht => ?_) (fun v => ⟨(hrow k hk.symm v).2.1, ?_⟩) hv hA
  · have := hχ i hi _ (Y.side i s) (Y.jS_range i s).1 (Y.jS_range i s).2 k hk _ (D.naut.plGw_over k v) _
      (D.nd.plOm.2 _) t ht _ (cConj_apply Y t)
    rw [← map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, map_inv]
    exact congrArg _ this
  · obtain ⟨u, hu, e⟩ := h3.2.2.2.2.2 k hk v
    exact ⟨_, D.ntypes.tg_mem k v, fun h0 => (hrow k hk.symm v).2.2 _ u hu (e ▸ h0)⟩
end Comparison₂
theorem adm2_of_isTriple_wildOne (D : D7) (hT : _root_.GlobalTheory.Triple.IsGaloisTriple D) (hW : WildOne D) : BlochKatoReduction.adm2 D := _root_.GlobalTheory.TripleAdm.gen_adm2_of_isTripleOf hT hW
end GlobalTheory.TripleAdm
end
end
