import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Frob
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
end Frob
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Eps
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
end Eps
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
theorem exists_stringRep_alt_alt (D : D7) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)) (hBC : IsBCV D.nd D.naut i P Pa) (p : Part D.naut.CG) (hp : p ∈ Pa) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)), UpperTheory.GalS.IsStringRepN D i p ρ := by
  obtain ⟨⟨⟨hLP, hAut, hGal⟩, -, -, hG, -, -, -⟩, -⟩ := hA.1
  obtain ⟨ha, hd, hc⟩ := hBC.1 p hp
  have hw := GlobalTheory.BCGal.galois_relation_away_from_l D.nd D.naut i hLP hAut hGal (_root_.UpperTheory.GalS.weak' hG) ha p.π hc
    ((p.d : ℤ) - 1 + p.a - D.R.nV) fun τ => by
    have hW : (D.naut.infWt i τ).Nodup ∧
        ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
      rw [D.nbc.embAV_inf i P]
      exact D.nbc.infW_alg _ _ τ
    have hle : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ D.naut.infWt i τ := by
      rw [← hBC.2.2.2.2.2 τ]
      refine le_trans (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ ?_)
        (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
      exact List.mem_map.2 ⟨0, by simp; exact ⟨0, by omega, by simp⟩, by simp⟩
    refine ⟨(Multiset.nodup_of_le hle hW.1).of_map _, fun z hz => ?_⟩
    obtain ⟨n, hn⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
    exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
  obtain ⟨ρ, hcont, hss, hwd⟩ := hw
  refine ⟨ρ, hcont, hss, fun w hwl => ?_⟩
  convert hwd w hwl using 2
  push_cast
  ring_nf
theorem stringDecomp_holds_alt_alt :
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ r, GoodR D.nd i r →
    ∃ R : ∀ k : Fin Pa.length, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)),
      (∀ k, UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) ∧
      ∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a) := by
  intro D hA i x P Pa hx hBC r hr
  have hC := hA.1.1.2.2.2.2.2.2.2.2.1
  have hex : ∀ p : Part D.naut.CG, ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)),
      p ∈ Pa → UpperTheory.GalS.IsStringRepN D i p ρ := by
    intro p
    by_cases hp : p ∈ Pa
    · obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.StringDecomp.exists_stringRep_alt_alt D hA i P Pa hBC p hp
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose Rp hRp using hex
  refine ⟨fun k => Rp (Pa.get k), fun k => hRp _ (List.get_mem Pa k), ?_⟩
  have hrk : rkL Pa = D.R.nV := (rkL_eq Pa).trans hBC.2.2.1
  have hcL := cont_listRep Rp _ (cont_epsQU_inv D.nd D.naut i) Pa (fun p hp => (hRp p hp).1)
  obtain ⟨ρ', hρ'⟩ := exists_cast hrk (listRep Rp (epsQU D.nd D.naut i)⁻¹ Pa)
  have hQ := GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois D i x (r x) (hr x)
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
    ((placesOver_finite' D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have key := GlobalTheory.charpoly_eq_of_eqOn_dense
    (fun g => ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))))
    (fun g => ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))))
    hQ.1 (hρ'.1 hcL) _ (dense_iff_closure_eq.2 (hC _ hfin)) (by
      rintro σ ⟨w, hw, hsp, B, hB, hσ⟩
      simp only [Set.mem_union, not_or, Finset.mem_coe] at hw
      have hso : SplitOut D.nd i w := ⟨hsp, hw.1.1, hw.1.2, hw.2⟩
      show _ = _
      rw [hQ.2.2 w hso B σ hB hσ, hρ'.2 σ, charpoly_listRep]
      apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
      rw [Polynomial.map_map, show (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) =
        ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
        from rfl, D.naut.pt_loc i P x hx w hso, ← hBC.2.2.2.1 w hsp]
      exact (iso_poly i w hso.2.1 B σ hB hσ Rp _ _ (epsQU_frob D.nd D.naut i hso.2.1 hB hσ) Pa
        (fun p hp => (hRp p hp).1) (fun p hp => ((hRp p hp).2.2 w hso.2.1).eq_of_unr ((D.naut.unr_tw _ _).2
          (UpperTheory.GalN.unr_part Pa (iso_unr i hBC w hso) p hp (hBC.1 p hp).2.1))) (iso_unr i hBC w hso)).symm)
  intro g
  rw [key g, hρ'.2 g, charpoly_listRep, epsQU_inv_val, ← prod_get]
  rfl
end GlobalTheory.StringDecomp
end
end
