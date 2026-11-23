import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pStabKer :
    FacEq → KNFact → CongGrpEx → StabKer := by
  intro _ hKN hCG E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ _ r W haux N _ _ L hw Ty hTy k hk hkr
  obtain ⟨k', hk', hlev, hJ, hχ⟩ := hk
  have hK : k ∈ Ty.K := by
    refine (hTy.K_iff k).2 ⟨⟨k', hk', hlev⟩, fun w hwW => ?_⟩
    have hr : (r : 𝓞 E) ∈ w.1.asIdeal := haux.half.above w hwW
    obtain ⟨K, hK, -, -, -, -, hIw, -⟩ := hCG E n r haux.prime.pos w.1
    have hf := hKN E A n p S F w (L w) (hTy.fac w) r haux.prime haux.good hr r haux.prime.pos K hK
    exact hIw hr (hf.2 k hkr)
  refine (Ty.mem_kerK k).2 ⟨hK, ?_⟩
  have hpr : Ty.L.pr k = comp w₀ k' := by
    rw [hTy.L_eq, ← hk']
    exact (hTy.fac ⟨w₀, hw⟩).1 k'
  refine (hTy.ψ_eq _ ⟨comp w₀ (F.th k'), hJ⟩ ?_).trans hχ
  simp only [hpr, th_eq F, CertificateRingHomMap.comp_th, CertificateRingHomMap.invT_val]
