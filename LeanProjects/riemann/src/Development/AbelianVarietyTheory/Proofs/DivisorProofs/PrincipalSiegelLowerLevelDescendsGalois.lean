import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedDataTransportIdentityLevelChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDescentFiniteEtaleSurjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PrincipalDescent

theorem principal_descends : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [IsNoetherianRing o] [CommRing o'] (b : TBase o n) (ζ' : o') (j : o →+* o') (X Y : Scheme.{0}) (s' : X ⟶ Sp o') (π : X ⟶ Y) (sY : Y ⟶ Sp o) (C : SiegPre h N ζ' s') (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ν : Ga → (C.A.left ⟶ C.A.left)), N ≠ 0 → IsUnit (N : o') → n ∣ N → j (b.ζ : o) = ζ' ^ (N / n) → π ≫ sY = s' ≫ spMap j → IsGaloisCover Ga ρ π → IsQProjOver (π ≫ sY) → LocallyOfFiniteType sY → C.Principal → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → (∀ a, SRelBy C C (N / n) (N / n) (ρ a) (ν a)) → ∃ c : SiegPre h n (b.ζ : o) sY, c.Principal ∧ SRel C c (N / n) 1 π := by
  intro h n N o o' _ _ _ b ζ' j X Y s' π sY C Ga _ ρ ν hN hNu hdiv hζ hbase hπ hq hft hP ν1 νm hν
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨c, hCc, -⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o' b.ζ ζ' j X s' C hN hNu hdiv hζ
  have hqA : IsQProjOver (C.A.hom ≫ π ≫ sY) := GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian o X (π ≫ sY) C.A C.diag hq (pull_isLB C.isLB _) hP.1
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ := GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base o X Y π sY Ga ρ C.A ν hπ hqA C.ab (fun a => (hν a).1) ν1 νm
  obtain ⟨P₀, φ₂, hP₀, sq, iso, norm⟩ := GlobalTheory.T.exists_squareBundle_descent_galoisCover X Y π Ga ρ C.A A₀ φ ν C.P hπ C.ab hA₀ gp hφ (fun a => (hν a).1) ν1 νm
    C.isLB C.rig₁ (fun a => (hν a).2.1)
  have hlev : ∀ a, ∃ x₀ : 𝟙_ (Over Y) ⟶ A₀, (C.lev a ^ (N / n)).left ≫ φ = π ≫ x₀.left := by
    intro a
    obtain ⟨f, hf, -⟩ := hπ.existsUnique_desc ((C.lev a ^ (N / n)).left ≫ φ) (fun g => by
      rw [← Category.assoc, ← (hν g).2.2 a, Category.assoc, hφ.inv g])
    have hf' : f ≫ A₀.hom = 𝟙 Y := by
      have := hπ.fin
      have := hπ.etale
      have := hπ.onto
      have : Epi π := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi π, ← Category.assoc, hf, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
      simp
    exact ⟨Over.homMk f hf', hf.symm⟩
  choose lev₀ hlev₀ using hlev
  obtain ⟨φ', φ₂', gp', sq', iso', hlev'⟩ := GlobalTheory.T.descendedData_transport_identity_levelChange h n N (N / n) o o' b.ζ ζ' X Y (s' ≫ spMap j) s' C c π A₀ φ φ₂ P₀ lev₀
    hCc gp sq hP₀ iso hlev₀
  obtain ⟨c₀, hpb⟩ := GlobalTheory.T.exists_siegelObject_of_galois_descended_data h n o b.ζ X Y π (s' ≫ spMap j) sY Ga ρ c A₀ φ' φ₂' P₀ lev₀ hbase.symm hπ hA₀ gp' sq' hP₀
    iso' norm hlev'
  have hR : SRel C c₀ (N / n) 1 π := by
    have e := ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n N o o o' b.ζ b.ζ ζ' Y X X sY (s' ≫ spMap j) s' c₀ c C π (𝟙 X) 1 1 (N / n)
      ((sRel_one_one_iff c c₀ π).2 hpb)).1).1 hCc
    rwa [Category.id_comp] at e
  exact ⟨c₀, GlobalTheory.T.principal_descent_finite_etale_surjective h N n (N / n) 1 o' o ζ' b.ζ X Y s' sY π C c₀ hπ.fin hπ.etale hπ.onto hR hP, hR⟩

end GlobalTheory.PrincipalDescent
