import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKDSupUnitIdlIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLaws

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.Mem.Chr.RelDet GlobalTheory.Mem.Chr.IdlFact
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetLat

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem ordSub_conj {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ P) (detSub N) = -ordSub P (detSub N) := by
  have h := CharValCompare.val_dual (P := P) ⟨hN, hu⟩ (isFr_latFr P hN) (isFr_latFr (conjPrime₂ P) hN)
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq hN (isFr_latFr P hN), ordSub_detSub_eq hN (isFr_latFr (conjPrime₂ P) hN)]
  unfold ordF
  rw [eq_inv_of_mul_eq_one_right h, WithZero.log_inv]

theorem ordSub_std (w : HeightOneSpectrum (𝓞 E)) : ordSub w (detSub (stdLat E n)) = 0 := by
  rw [ordSub_detSub_eq (f := 1) stdLat_lattice fun _ => Iff.rfl]
  simp [ordF]

open Classical in

theorem ordI_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    {fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n} (hf : ∀ P, IsFr P N (fr P)) (w : HeightOneSpectrum (𝓞 E)) :
    ordI w (detIdl SB N fr) =
      if w ∈ SB then ordSub w (detSub N) else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub N)).toNat : ℤ) := by
  have e : valAt w (detIdl SB N fr) = Valued.v (compAt w (detIdl SB N fr)) := valAt_apply _ _
  rw [ordI, e, compAt_detIdl SB hN]
  split_ifs
  · rw [valued_algebraMap, ordSub_detSub_eq hN (hf w)]
    rfl
  · simp
  · have h := ordF_unif_self w
    unfold ordF at h
    rw [map_pow, valued_algebraMap, WithZero.log_pow, neg_eq_iff_eq_neg.1 h]
    simp

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_mk_eq_of_ord {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {a b : Ideles H.E}
    (h : ∀ w, ordI w a - ordI (conjPrime₂ w) a = ordI w b - ordI (conjPrime₂ w) b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtQ H SQ ⧸ UOQ H SQ) = QuotientGroup.mk (QuotientGroup.mk b) := by
  refine QuotientGroup.eq.2 ?_
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_mem_UOQ, KDq_sup_unitIdl]
  refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
  rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv,
    (isConjPl_iff H w w').1 hw]
  have := h w
  congr 1
  omega

end GlobalTheory.Mem.Col2.DetLat

namespace GlobalTheory.Mem.Col2

open DetLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_detPt_eq_relDetQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → (QuotientGroup.mk (detPt H SQ p) : DtQ H SQ ⧸ UOQ H SQ) = relDetQ H SQ n (stdLat H.E n) p.deco.1.N := by
  intro R H n ST SG Q SQ p hL
  have hN := p.deco.2.lat
  have hf : {w | (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat ≠ 0}.Finite :=
    (finite_ordSub hN).subset fun v hv h0 => hv (by simp [h0, ordSub_std])
  refine mk_mk_eq_of_ord H SQ (a := ptIdl H SQ p)
    (b := powI fun w => (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat) fun w => ?_
  rw [ordI_powI _ hf, ordI_powI _ hf, ptIdl, ordI_detIdl _ hN (isFr_ptFr p), ordI_detIdl _ hN (isFr_ptFr p),
    CharValCompare.conjP_conjP, ordSub_std, ordSub_std, ordSub_conj hN p.deco.2.uni]
  have hs := hL.split w
  by_cases h1 : w ∈ uSG SG SQ
  · rw [if_pos h1, if_neg (hs h1), if_pos h1]
    omega
  · by_cases h2 : conjPrime₂ w ∈ uSG SG SQ
    · rw [if_neg h1, if_pos h2, if_pos h2]
      omega
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
      omega

end GlobalTheory.Mem.Col2
