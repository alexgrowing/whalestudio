import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitUnitaryGroupIsoGlStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem map_eq_of_mem (e : G ≃ₜ* H) (A : Subgroup G) (A' : Subgroup H) (h : ∀ g, g ∈ A ↔ e g ∈ A') :
    A' = A.map (e : G →* H) := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩
  · rintro ⟨g, hg, rfl⟩
    exact (h g).1 hg

theorem cptPart_map_equiv (e : G ≃ₜ* H) (T : Subgroup G) :
    cptPart (T.map (e : G →* H)) = (cptPart T).map (e : G →* H) := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hz : ∀ t, (Subgroup.zpowers ((e : G →* H) t) : Set H) = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    rfl
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((e : G →* H) t) : Set H)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem twCent_mem (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (he : ∀ g, e (θ g) = θ' (e g)) (δ g : G) :
    g ∈ twCent θ δ ↔ e g ∈ twCent θ' (e δ) := by
  rw [mem_twCent, mem_twCent, ← he, ← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm

theorem summand_map (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G)
    (f : G → ℂ) (f' : H → ℂ) (he : ∀ g, e (θ g) = θ' (e g)) (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    (hf : ∀ g, f' (e g) = f g) (y : G) :
    summand θ' K' (e δ) f' (e y) = summand θ K δ f y := by
  have hT : twCent θ' (e δ) = (twCent θ δ).map (e : G →* H) :=
    map_eq_of_mem e _ _ (twCent_mem e θ θ' he δ)
  have hK' : K' = K.map (e : G →* H) := map_eq_of_mem e _ _ hK
  subst hK'
  unfold summand
  congr 1
  · have h1 : (K.map (e : G →* H)).map (MulAut.conj (e y)).toMonoidHom =
        (K.map (MulAut.conj y).toMonoidHom).map (e : G →* H) := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    rw [h1, hT, ← Subgroup.map_inf_eq _ _ _ e.injective, cptPart_map_equiv,
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]
  · let ψ : K ≃* (K.map (e : G →* H)) := e.toMulEquiv.subgroupMap K
    rw [← GlobalTheory.BCT.OrbProd.avg_comp_equiv ψ]
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [← hf]
    congr 1
    show (e y * e k.1)⁻¹ * e δ * θ' (e y * e k.1) = _
    rw [← map_mul, ← he, ← map_inv, ← map_mul, ← map_mul]

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

def dcMap (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) :
    DoubleCoset.Quotient (T : Set G) (K : Set G) → DoubleCoset.Quotient (T' : Set H) (K' : Set H) :=
  fun q => DoubleCoset.mk T' K' (e (Quotient.out q))

theorem dcMap_bij (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) (hT : ∀ g, g ∈ T ↔ e g ∈ T')
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') : Function.Bijective (dcMap e T K T' K') := by
  constructor
  · intro q1 q2 h
    obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ _ _).1 h
    rw [← DoubleCoset.out_eq' T K q1, ← DoubleCoset.out_eq' T K q2, DoubleCoset.eq]
    refine ⟨e.symm a, (hT _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    exact hab
  · intro q'
    refine ⟨DoubleCoset.mk T K (e.symm (Quotient.out q')), ?_⟩
    obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul T K (e.symm (Quotient.out q'))
    unfold dcMap
    rw [hab]
    conv_rhs => rw [← DoubleCoset.out_eq' T' K' q']
    rw [DoubleCoset.eq]
    refine ⟨(e a)⁻¹, T'.inv_mem ((hT a).1 ha), (e b)⁻¹, K'.inv_mem ((hK b).1 hb), ?_⟩
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    group

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

theorem twOrb_transport : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G) (f : G → ℂ) (f' : H → ℂ), (∀ g, e (θ g) = θ' (e g)) → (∀ g, g ∈ K ↔ e g ∈ K') → (∀ g, f' (e g) = f g) → twOrb θ K δ f = twOrb θ' K' (e δ) f' := by
  intro G H _ _ _ _ _ _ e θ θ' K K' δ f f' he hK hf
  have hT := twCent_mem e θ θ' he δ
  rw [twOrb_eq, twOrb_eq,
    ← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK))]
  refine finsum_congr fun q => ?_
  obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e δ)) K' (e (Quotient.out q))
  have e2 : Quotient.out (Equiv.ofBijective _ (dcMap_bij e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK) q) =
      a * e (Quotient.out q) * b := hab
  rw [e2, summand_rep θ' K' (e δ) f' _ ha hb, summand_map e θ θ' K K' δ f f' he hK hf]

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cPl_eq {u : Pl E} (hu : ¬ IsSplitAt u) : cPl E u = u :=
  (GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 hu

theorem orb_eq {u : Pl E} (hu : ¬ IsSplitAt u) : orb E u = {u} := by
  simp [orb, cPl_eq hu]

theorem pLoc_idem (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem pLoc_prjG_of_mem (T : Finset (Pl E)) (w : Pl E) (hw : w ∈ T) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T x) = GeneralLinearGroup.map (pLoc E w) x := by
  ext i j
  simp [prjG, prjM, pLoc_idem, hw, Matrix.one_apply]
  split_ifs <;> simp [map_sub, pLoc_idem, hw]

theorem pLoc_prjG_of_not_mem (T : Finset (Pl E)) (w : Pl E) (hw : w ∉ T) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T x) = 1 := by
  ext i j
  simp [prjG, prjM, pLoc_idem, hw, Matrix.one_apply]
  split_ifs <;> simp [map_sub, pLoc_idem, hw]

end GlobalTheory.EulerTw.Inert

namespace GlobalTheory.EulerTw.Inert

open GlobalTheory.EulerTw

theorem gam_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (u w : Pl E) (hw : w ∉ orb E u)
    (g : Gam E n u) : GeneralLinearGroup.map (pLoc E w) g.1 = 1 := by
  obtain ⟨x, hx⟩ := g.2
  rw [← hx]
  exact pLoc_prjG_of_not_mem _ _ hw x

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (GLw n w), IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' → ∀ φ : ∀ w : Pl E, GLw n w → ℂ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → ∀ δ : GL (Fin n) E, (δ * thE E n δ).val.charpoly.Separable → ∀ u ∈ S, ¬ IsSplitAt u → twOrb (GlobalTheory.EulerTw.thU E n u) (GlobalTheory.EulerTw.KU E n u) (GlobalTheory.EulerTw.pfU E n u (ratF E n δ)) (GlobalTheory.EulerTw.FU E n S φ u) = twOrb (thL n u) (GlobalTheory.LFun.KGL u n) (locEl n u δ) (φ u) := by
  intro E _ _ _ hU n S hS K' hK' φ hφ δ hδ u huS hu
  obtain ⟨e, he⟩ := GlobalTheory.T.nonsplit_unitary_group_iso_gl E n u hu
  have hcj := ((GlobalTheory.ConjAtPlace.main E hU u).2.2.2.1 hu).2.2.1
  have hmem : u ∈ orb E u := by simp [orb]
  rw [GlobalTheory.EulerTw.Transport.twOrb_transport (Gam E n u) (GLw n u) e (thU E n u) (thL n u) (KU E n u) (GlobalTheory.LFun.KGL u n) _
    (FU E n S φ u) (φ u) ?_ ?_ ?_]
  · congr 1
    rw [he]
    show GeneralLinearGroup.map (pLoc E u) (prjG E n (orb E u) (ratF E n δ)) = locEl n u δ
    rw [pLoc_prjG_of_mem _ _ hmem]
    simp only [locEl, if_neg hu, ratF]
    ext i j
    rfl
  · intro g
    rw [he, he]
    show GeneralLinearGroup.map (pLoc E u) (prjG E n (orb E u) (thF E n g.1)) = _
    rw [pLoc_prjG_of_mem _ _ hmem, thL, if_neg hu, thF]
    exact GlobalTheory.ThetaPull.map_thetaGL (pLoc E u) _ (cj u) hcj g.1
  · intro g
    rw [he, KU, Subgroup.mem_subgroupOf, Kglob, Subgroup.mem_iInf]
    constructor
    · intro h
      exact h u
    · intro h w
      rw [Subgroup.mem_comap]
      by_cases hw : w = u
      · subst hw
        exact h
      · rw [gam_one u w (by rw [orb_eq hu]; simpa using hw) g]
        exact one_mem _
  · intro g
    have h1 : S ∩ ↑(orb E u) = {u} := by
      rw [orb_eq hu]
      ext w
      simp only [Set.mem_inter_iff, Finset.coe_singleton, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨huS, rfl⟩
    have h2 : Sᶜ ∩ ↑(orb E u) = ∅ := by
      rw [orb_eq hu]
      ext w
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Finset.coe_singleton, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro hw rfl
      exact hw huS
    rw [FU, h1, h2, finprod_mem_singleton, finprod_mem_empty, mul_one, he]

end GlobalTheory.EulerTw.Inert
