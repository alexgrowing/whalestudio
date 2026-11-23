import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrrE
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.StrongIrrOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCoset
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCosetE

open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

namespace UpperTheory.V.Pr

private lemma open_basis {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (O : Set G) (hO : IsOpen O) (h1 : (1 : G) ∈ O) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ (V : Set G) ⊆ O := by
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  exact ⟨H.toSubgroup, H.isOpen', hH⟩

private lemma strong_of {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {m : ℕ} (G' V : Subgroup G) (hV : IsOpen (V : Set G))
    (r : G →* GL (Fin m) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r)) :
    StrongIrr (r.comp (V ⊓ G').subtype) := by
  refine strongIrrOfOpen _ κ m _ (fun f => (hc f).preimage continuous_subtype_val) ?_
  intro U hU W hW
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ O := by
    have : (1 : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := U.one_mem
    rw [← hOU] at this
    exact this
  obtain ⟨V', hV', hsub⟩ := open_basis (O ∩ V) (hO.inter hV) ⟨h1, V.one_mem⟩
  refine hirr V' hV' W fun g hg => ?_
  have h2 := hsub hg.1
  have h3 : (⟨g, h2.2, hg.2⟩ : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := by
    rw [← hOU]; exact h2.1
  exact hW _ h3

private lemma coset_in {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (U : Set G) (hU : IsOpen U) (s : G) (hs : s ∈ U) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ h ∈ V, s * h ∈ U := by
  obtain ⟨V, hV, hsub⟩ := open_basis ((fun h => s * h) ⁻¹' U) (hU.preimage (continuous_const.mul continuous_id))
    (by simpa using hs)
  exact ⟨V, hV, fun h hh => hsub hh⟩

private lemma cosetI {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {n : ℕ} (hn : n ≤ 3) (G' : Subgroup G)
    (r : G →* GL (Fin n) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r))
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin n → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  obtain ⟨h, hh⟩ := regCoset _ κ n hn _ (strong_of G' V hV r hc hirr) ⟨u, hu⟩ α hα hch (r s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  simp only [gm, map_mul, Units.val_mul]
  exact hh

private lemma sub_eq {κ : Type} (M : Matrix (Fin 3) (Fin 3) κ) :
    M.submatrix ![0, 2] ![0, 2] = !![M 0 0, M 0 2; M 2 0, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def cornerHom {G κ : Type} [Group G] [Field κ] (r : G →* GL (Fin 3) κ)
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0) :
    G →* Matrix (Fin 2) (Fin 2) κ where
  toFun g := (gm r g).submatrix ![0, 2] ![0, 2]
  map_one' := by
    rw [sub_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gm]
  map_mul' g h := by
    obtain ⟨a1, a2, a3, a4⟩ := hb g
    obtain ⟨b1, b2, b3, b4⟩ := hb h
    simp only [gm] at a1 a2 a3 a4 b1 b2 b3 b4
    rw [sub_eq, sub_eq, sub_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gm, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, *]

private def midHom {G κ : Type} [Group G] [Field κ] (r : G →* GL (Fin 3) κ)
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0) : G →* κ where
  toFun g := gm r g 1 1
  map_one' := by simp [gm]
  map_mul' g h := by
    obtain ⟨a1, a2, a3, a4⟩ := hb g
    simp only [gm] at a1 a2 a3 a4
    simp [gm, Matrix.mul_apply, Fin.sum_univ_three, *]

private lemma charpoly_block {κ : Type} [Field κ] (M : Matrix (Fin 3) (Fin 3) κ)
    (hb : M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0) :
    M.charpoly = (M.submatrix ![0, 2] ![0, 2]).charpoly * (X - C (M 1 1)) := by
  obtain ⟨a1, a2, a3, a4⟩ := hb
  rw [sub_eq]
  simp only [Matrix.charpoly, det_fin_three, det_fin_two]
  simp [charmatrix_apply, *]
  ring

private lemma cosetE {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] (G' : Subgroup G)
    (r : G →* GL (Fin 3) κ) (hc : LinClosed (gm r))
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0)
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') fun g => (gm r g).submatrix ![0, 2] ![0, 2])
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin 3 → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  let σ : G →* GL (Fin 2) κ := (cornerHom r hb).toHomUnits
  let ψ : G →* κˣ := (midHom r hb).toHomUnits
  have hσ : ∀ g, gm σ g = (gm r g).submatrix ![0, 2] ![0, 2] := fun g => rfl
  have hψ : ∀ g, ((ψ g : κˣ) : κ) = gm r g 1 1 := fun g => rfl
  have hcp : ∀ g, (gm r g).charpoly = (gm σ g).charpoly * (X - C ((ψ g : κˣ) : κ)) := fun g =>
    charpoly_block _ (hb g)
  have hcσ : LinClosed (gm σ) := fun f =>
    hc (f ∘ₗ
      { toFun := fun M : Matrix (Fin 3) (Fin 3) κ => M.submatrix ![0, 2] ![0, 2]
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
  obtain ⟨k, hk⟩ : ∃ k, α k = ψ u := by
    have h1 := congrArg (Polynomial.eval ((ψ u : κˣ) : κ)) ((hcp u).symm.trans hch)
    rw [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, eval_prod, eq_comm, Finset.prod_eq_zero_iff] at h1
    obtain ⟨k, -, hk⟩ := h1
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
    exact ⟨k, Units.ext hk.symm⟩
  have hch2 : (gm σ u).charpoly = ∏ i : Fin 2, (X - C ((α (k.succAbove i) : κˣ) : κ)) := by
    have h1 := (hcp u).symm.trans hch
    rw [Fin.prod_univ_succAbove _ k, hk, mul_comm] at h1
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) h1
  have hfree : FreeRatios ![α (k.succAbove 0), α (k.succAbove 1), ψ u] := by
    have e : ![α (k.succAbove 0), α (k.succAbove 1), ψ u] = α ∘ ![k.succAbove 0, k.succAbove 1, k] := by
      funext i
      fin_cases i <;> simp [hk]
    have inj : Function.Injective (![k.succAbove 0, k.succAbove 1, k] : Fin 3 → Fin 3) := by
      clear hk hch2 e
      revert k
      decide
    rw [e]
    exact fun i j hij => hα _ _ (inj.ne hij)
  obtain ⟨h, hh⟩ := regCosetE _ κ _ (ψ.comp (V ⊓ G').subtype) (strong_of G' V hV σ hcσ hirr) ⟨u, hu⟩
    (fun i => α (k.succAbove i)) hfree hch2 (σ s) (ψ s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  rw [hcp]
  simp only [gm, map_mul σ, map_mul ψ, Units.val_mul (σ s)]
  exact hh

private lemma charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, h2⟩ := hg s
  have h3 := Matrix.charpoly_of_upperTriangular ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    (fun i j hij => h1 i j hij)
  simp only [h2] at h3
  rw [← h3, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  rfl

end UpperTheory.V.Pr

theorem UpperTheory.V.Pr.nice_specialization_twist_satisfies_third_condition :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → y.N3 := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hnice hρ hψ U hU hne
  haveI : CompactSpace T.G.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ T.G.η_open).isCompact
  let r : T.G.G₀ →* GL (Fin n) y.Fb := W.pushRep (algebraMap y.Fr y.Fb) y.ρF
  have hr : ∀ g, gm r g = (W.mat y.ρF g).map (algebraMap y.Fr y.Fb) := fun g => rfl
  have hc : LinClosed (gm r) :=
    linClosedOfAdic T.G.G₀ y.A y.Fb ((algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr))
      ((algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)) n (fun g => W.mat y.ρ g) y.cont
  obtain ⟨v⟩ : Nonempty T.G.Vl := by
    rw [T.K.e.nonempty_congr]
    by_contra h
    rw [not_nonempty_iff] at h
    have := T.big.1
    simp [Fr.Frame.d] at this
  have hsep : ∀ V : Subgroup T.G.G₀, IsOpen (V : Set T.G.G₀) → ∃ u ∈ V ⊓ T.G.G', ∃ α : Fin n → y.Fbˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : y.Fbˣ) : y.Fb)) := by
    intro V hV
    obtain ⟨g, hg, hfree⟩ := niceSep l O F n T x L y j hj hnice hρ hψ V hV v
    refine ⟨_, hg, fun i => Units.map (algebraMap y.Fr y.Fb).toMonoidHom
      (Units.map (algebraMap y.A y.Fr).toMonoidHom (y.ψ v i g)), fun a b hab m hm h => hfree a b hab m hm ?_, ?_⟩
    · refine Units.map_injective (f := (algebraMap y.Fr y.Fb).toMonoidHom) (algebraMap y.Fr y.Fb).injective ?_
      rw [map_pow, map_pow]
      exact h
    · have h1 : (W.mat y.ρF (T.G.φ v g)).charpoly = _ := charpoly_flag _ _ (y.flag v) g
      rw [hr, Matrix.charpoly_map, h1, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, map_X, map_C]
      rfl
  suffices h : ∃ σ ∈ U ∩ (T.G.G' : Set T.G.G₀), (gm r σ).charpoly.Separable by
    obtain ⟨σ, h1, h2⟩ := h
    rw [hr, Matrix.charpoly_map, Polynomial.separable_map] at h2
    exact ⟨σ, h1, h2⟩
  by_cases hE : n = 3 ∧ L.ρ.ee ≤ RingHom.ker j
  · obtain ⟨rfl, hE⟩ := hE
    have hz : ∀ g a b, Odd (Fr.w 3 a - Fr.w 3 b) → gm r g a b = 0 := by
      intro g a b hab
      have h1 : j (L.ρ.r (T.K.π g) a b) = 0 := hE (Ideal.subset_span ⟨_, a, b, hab, rfl⟩)
      have h2 : W.mat y.ρ g a b = 0 := by
        rw [hρ]
        show _ * j (L.ρ.r (T.K.π g) a b) = 0
        rw [h1, mul_zero]
      show algebraMap y.Fr y.Fb (algebraMap y.A y.Fr (W.mat y.ρ g a b)) = 0
      rw [h2, map_zero, map_zero]
    exact cosetE T.G.G' r hc
      (fun g => ⟨hz g 0 1 (by decide), hz g 1 0 (by decide), hz g 1 2 (by decide), hz g 2 1 (by decide)⟩)
      (niceIrrE l O F T x L y j hj hnice hρ hψ ⟨hnice.off, rfl, hE⟩) hsep U hU hne
  · exact cosetI (by rcases T.n23 with h | h <;> omega) T.G.G' r hc
      (niceIrr l O F n T x L y j hj hnice hρ hψ ⟨hnice.off, fun h3 h => hE ⟨h3, h⟩⟩) hsep U hU hne
