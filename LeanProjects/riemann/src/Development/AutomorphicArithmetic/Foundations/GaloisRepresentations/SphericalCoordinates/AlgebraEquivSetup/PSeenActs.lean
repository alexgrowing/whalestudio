import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pSeenActs :
    MemSum → MemAct → MemDeck → SeenShape → LevBasic → KNIdx → SeenActs := by
  intro hS hA hD hSh hLB _ E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hTy g θ hseen
  have hK : g.K ≤ Ty.kerK := (hSh E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hTy g θ hseen).1
  have hK₀ : Ty.K₀ = S.L.KN N.1 := hTy.K₀_eq
  have hker : Ty.kerK ≤ Ty.K := fun k hk => ((Ty.mem_kerK k).1 hk).1
  have hnorm : ∀ M : ℕ, ∀ k ∈ S.L.KN 1, ∀ u ∈ S.L.KN M, k * u * k⁻¹ ∈ S.L.KN M := fun M k hk u hu =>
    (hLB p S.D S.G S.L).2.2.2.2.1 _ _ ((hLB p S.D S.G S.L).2.2.1 M) k hk u hu
  have hnormK : ∀ k ∈ g.K, ∀ u ∈ S.L.KN g.M.1, k * u * k⁻¹ ∈ S.L.KN g.M.1 := fun k hk =>
    hnorm _ k (g.le_one hk)
  have hidx : (S.L.KN g.M.1).relIndex g.K ≠ 0 := fun h0 =>
    GlobalTheory.W2.relIndex_KN_ne_zero S.L one_pos (by have := g.M.2.1; omega) (Subgroup.relIndex_eq_zero_of_le_right g.le_one h0)
  refine ⟨fun a ha => ?_, fun hd hh => ?_, fun M' _ L' Kw t z hf hf' hap hz he => ?_⟩
  · obtain ⟨k, hk, hka⟩ := (hS _ g.K (S.L.KN g.M.1) (S.L.KN N.1) g.h g.le hidx hnormK g.adm).2.1 a ha
    exact ⟨k, hker (hK hk), Ty.le (hK₀ ▸ hka)⟩
  · obtain ⟨h1, h2, h3⟩ := hd
    have := hD _ _ Ty Ty.kerK (Ty.triv_of_le le_rfl) g.h hh (fun u hu => by
      rw [hK₀] at hu ⊢; exact hnorm _ _ h3 u hu)
    rw [hK₀] at this
    have e : g.fn = memFn (S.L.KN N.1) (S.L.KN N.1) (S.L.KN N.1) g.h := by
      have : g.fn = memFn g.K (S.L.KN g.M.1) (S.L.KN N.1) g.h := rfl
      rw [this, h1, h2]
    rw [e]; exact this
  · have := hA _ _ _ Ty L' Kw hf hap g.K (S.L.KN g.M.1) (Ty.triv_of_le hK) hf' (hK₀ ▸ g.le)
      (hK₀ ▸ KN_anti g.dvd) hidx hnormK t z g.h hz he (hK₀ ▸ g.adm)
    rw [hK₀, ← he] at this
    exact this
