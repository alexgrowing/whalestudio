import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pMemFn :
    SeenShape → SeenActs → ActsConv → TyFact → MemFn := by
  intro hSh hAc hAC hTF E _ _ _ A n p _ S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨-, hcase⟩ := hSh E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨hsupp, hdeck, hgen⟩ := hAc E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨tf1, tf2, -⟩ := hTF E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy
  rcases hcase with ⟨hD, hh, hθ⟩ | ⟨w, t, z, i, B, hFree, hAp, -, -, -, -, -, hinv, hCen, hWpr, hFg, -⟩
  · have hA := hdeck hD hh
    have hhK : g.h ∈ Ty.K := ((Ty.mem_kerK _).1 hh).1
    refine ⟨hA.1, ?_, Or.inl ⟨hD, hθ, ?_⟩⟩
    · intro a ha u hu
      obtain ⟨k, hk, hka⟩ := hsupp a ha
      have haK : a ∈ Ty.K := by
        have e : a = (g.h * k)⁻¹ * (g.h * k * a) := by group
        rw [e]
        exact Ty.K.mul_mem (Ty.K.inv_mem (Ty.K.mul_mem hhK hk)) hka
      exact (tf1 u hu).1.2 a haK
    · have e := (hAC _ _ Ty _ _ _ hA).1
      rwa [one_smul] at e
  · obtain ⟨hfac, hap⟩ := tf2 w hFree.2.1 hFree.2.2.1 hAp
    have hA := hgen _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hfac hFg hap hCen hinv
    have hpr : Ty.L.pr g.h = 1 := by
      have e := hA.2.1
      rwa [map_inv, inv_eq_one] at e
    refine ⟨hA.1, ?_, Or.inr ⟨hpr, hWpr, (hAC _ _ Ty _ _ _ hA).1⟩⟩
    intro a ha u hu
    obtain ⟨k, hk, hka⟩ := hsupp a ha
    have f := (tf1 u hu).1.2
    have e : (L u).pr (g.h * k * a) = (L u).pr k * (L u).pr a := by
      rw [map_mul, map_mul, hWpr u hu, one_mul]
    have h6 := f _ hka
    rw [e] at h6
    exact (Subgroup.mul_mem_cancel_left _ (f k hk)).1 h6
