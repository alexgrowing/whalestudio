import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem mapP_mapP {R B C ι : Type} [CommRing R] [CommRing B] [CommRing C] (f : R →+* B) (g : B →+* C)
    (N : Polynomial (MvPolynomial ι R)) : mapP g (mapP f N) = mapP (g.comp f) N := by
  simp only [mapP, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun p => MvPolynomial.map_map f g p

private theorem step_one (hPP : PtsProd) {R C C' ι J : Type} [CommRing R] [CommRing C] [CommRing C'] [Algebra R C]
    [Fintype ι] [Fintype J] (S : J → Type) [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)]
    (N : J → Polynomial (MvPolynomial ι R)) (a : J → ℕ) (s : ∀ j, ι → S j) (ρ : C →+* C')
    (I : J → Type) [∀ j, Fintype (I j)] (z : ∀ j, I j → (S j →ₐ[R] C))
    (h : ∀ j, mapP (algebraMap R C) (N j) = ∏ i, form fun k => z j i (s j k)) :
    ((pts a fun j i k => ρ (z j i (s j k))).map form).prod = mapP (ρ.comp (algebraMap R C)) (∏ j, N j ^ a j) := by
  rw [hPP C C' ρ ι J I a (fun j i k => z j i (s j k))]
  simp_rw [← h]
  rw [← mapP_mapP]
  congr 1
  simp only [mapP, Polynomial.map_prod, Polynomial.map_pow]

theorem UpperTheory.Gal.crystallineComparison.sameNormRing_of :
    NormRead → ValLift → PtsProd → CongrRad → SameNormRing := by
  intro hNR hVL hPP hCR l R _ 𝔞 hB J _ S _ _ d hS a b ι _ s hV B _ _ hl I _ z hz B' _ ρ hρ
  choose N hN using fun j => hNR l (d j) R (S j) (hS j) hB.closed ι (s j)
  have hB1 : ∀ j, mapP (algebraMap R B) (N j) = ∏ i, form fun k => z j i (s j k) :=
    fun j => (hN j).1 B hl (I j) (z j) (hz j)
  have key : mapP (ρ.comp (algebraMap R B)) (∏ j, N j ^ a j) = mapP (ρ.comp (algebraMap R B)) (∏ j, N j ^ b j) := by
    refine hCR R 𝔞 hB.rad ι _ _ ?_ B' _ hρ
    intro 𝔭 hp
    haveI : 𝔭.IsPrime := hp.1.1
    obtain ⟨V, _, _, _, _, _, hl', hc⟩ := hVL R (l : R) hB.nzd 𝔭
    have hl0 : (l : V) ≠ 0 := by simpa using hl'
    refine ⟨IsLocalRing.ResidueField V, inferInstance, (IsLocalRing.residue V).comp (algebraMap R V), ?_, ?_⟩
    · rw [← RingHom.comap_ker, IsLocalRing.ker_residue, hc]
    · have hfin : ∀ j, Finite (S j →ₐ[R] V) := fun j => ((hN j).2 V hl0).1
      letI : ∀ j, Fintype (S j →ₐ[R] V) := fun j => @Fintype.ofFinite _ (hfin j)
      have hV1 : ∀ j, mapP (algebraMap R V) (N j) = ∏ i : S j →ₐ[R] V, form fun k => i (s j k) :=
        fun j => ((hN j).2 V hl0).2 (S j →ₐ[R] V) id Function.bijective_id
      have hm := hV V hl0 (by rw [hc]; exact hp) (fun j => S j →ₐ[R] V) (fun j i => i) (fun j => Function.bijective_id)
      rw [← step_one hPP S N a s (IsLocalRing.residue V) (fun j => S j →ₐ[R] V) (fun j i => i) hV1,
        ← step_one hPP S N b s (IsLocalRing.residue V) (fun j => S j →ₐ[R] V) (fun j i => i) hV1, hm]
  show ((pts a fun j i k => ρ (z j i (s j k))).map form).prod = ((pts b fun j i k => ρ (z j i (s j k))).map form).prod
  rw [step_one hPP S N a s ρ I z hB1, step_one hPP S N b s ρ I z hB1, key]
