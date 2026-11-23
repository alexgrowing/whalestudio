import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pPhiTy :
    PPart → LevSec → FacEq → UpperTheory.Gal.W2.Seed.LocComm → PhiTy := by
  intro hP hL hF hc E _ _ _ A n p _ S F x U w₀ Up V _ _ _ hOff _ r W hAux N hN hStab L hw Ty hTy
  have hj : F.j = F.tr.j := F.j_tr
  have h4 : ∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) →
      (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ GlobalTheory.LFun.KGL w n) →
      ∀ g, V.Φ (CertificateRingHomMap.th (g * k)) = V.Φ (CertificateRingHomMap.th g) := by
    intro k h1 h2 g
    have hk : CertificateRingHomMap.th k ∈ lev V.S V.Kw :=
      (hL E A n p S F.tr V.S V.Kw hOff.1).2 _
        (fun w hw' => by rw [CertificateRingHomMap.comp_th, h1 w hw', map_one])
        (fun w hw' => by rw [CertificateRingHomMap.comp_th]; exact CertificateRingHomMap.invT_mem_KGL (h2 w hw'))
        (fun u _ => one_mem _)
    have e : comp w₀ (CertificateRingHomMap.th k) = 1 := by rw [CertificateRingHomMap.comp_th, h1 _ hw.2, map_one]
    have hJ : comp w₀ (CertificateRingHomMap.th k) ∈ V.J := e ▸ one_mem _
    have hχ : V.χ ⟨comp w₀ (CertificateRingHomMap.th k), hJ⟩ = 1 := by
      have : (⟨comp w₀ (CertificateRingHomMap.th k), hJ⟩ : V.J) = 1 := Subtype.ext e
      rw [this, map_one]
    rw [map_mul, V.form.right _ hk hJ, hχ]
    simp
  have h3 : ∀ g : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g ∈ GlobalTheory.LFun.KGL w n) →
      V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j g))) = V.Φ (CertificateRingHomMap.th g) := by
    intro g hg
    obtain ⟨k, e, k1, k2, -⟩ := hP E A n p S F.tr g
    have := h4 k k1 (fun w hw' => by rw [k2 w hw']; exact hg w hw') (F.tr.sec (F.tr.j g))
    rw [← e] at this
    rw [hj]
    exact this.symm
  refine ⟨?_, ?_, h3, h4⟩
  · obtain ⟨g₀, h0, hg⟩ := hOff.2
    intro hz
    apply h0
    have e := congrFun hz (F.j (CertificateRingHomMap.th g₀))
    have e' : V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j (CertificateRingHomMap.th g₀)))) = 0 := e
    rw [h3 _ (fun w hw' => by rw [CertificateRingHomMap.comp_th]; exact CertificateRingHomMap.invT_mem_KGL (hg w hw')), CertificateRingHomMap.th_th] at e'
    exact e'
  · intro k hk g
    obtain ⟨⟨k', e, hk'⟩, -⟩ := (hTy.K_iff k).1 hk
    rw [th_eq] at hk'
    have hs : F.tr.sec k ∈ lev V.S (CertificateRingHomMap.levT V.Kw) := by
      have := (hL E A n p S F.tr V.S (CertificateRingHomMap.levT V.Kw) hOff.1).1 k' (CertificateRingHomMap.th_mem_lev.1 hk')
      rwa [← hj, e] at this
    have hs' := CertificateRingHomMap.th_mem_lev.2 hs
    have hpr : Ty.L.pr k = comp w₀ (F.tr.sec k) := by
      have h := (hF E A n p S F hc ⟨w₀, hw⟩).2 _ (hTy.fac ⟨w₀, hw⟩)
      rw [hTy.L_eq, h]
      rfl
    have hyy : (comp w₀ (CertificateRingHomMap.th (F.tr.sec k))).val = ((Ty.L.pr k)⁻¹).valᵀ := by
      rw [CertificateRingHomMap.comp_th, CertificateRingHomMap.invT_val, hpr]
    have hyJ : Ty.L.pr k ∈ Ty.J := Ty.fact.2 k hk
    have hJ' : comp w₀ (CertificateRingHomMap.th (F.tr.sec k)) ∈ V.J := (hTy.J_iff _ _ hyy).1 hyJ
    show V.Φ (CertificateRingHomMap.th (F.tr.sec (g * k))) = ((Ty.ψ ⟨Ty.L.pr k, Ty.fact.2 k hk⟩ : ℂˣ) : ℂ) • V.Φ (CertificateRingHomMap.th (F.tr.sec g))
    rw [map_mul, map_mul, V.form.right _ hs' hJ', hTy.ψ_eq ⟨_, hyJ⟩ ⟨_, hJ'⟩ hyy]
