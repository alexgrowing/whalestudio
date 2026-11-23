import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeSummandCriterionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumMemLoc
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual_iff (R : Subalgebra o Ω) {m : ℕ} {L : AddSubgroup (Fin m → Ω)}
    {v : Fin m → Ω} : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem std_le_dual (R : Subalgebra o Ω) {m : ℕ} {A : AddSubgroup (Fin m → Ω)}
    (h : A ≤ stdLat R (Fin m)) : stdLat R (Fin m) ≤ dotDual R A := by
  intro v hv
  rw [mem_dotDual_iff]
  intro l hl
  have hl' := (LatticeGoodness.mem_stdLat R).1 (h hl)
  have hv' := (LatticeGoodness.mem_stdLat R).1 hv
  show ∑ i, l i * v i ∈ R
  exact sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std (R : Subalgebra o Ω) {m : ℕ} {A : AddSubgroup (Fin m → Ω)} {w : Ω}
    (h : mulLat w (stdLat R (Fin m)) ≤ A) {v : Fin m → Ω} (hv : v ∈ dotDual R A) :
    w • v ∈ stdLat R (Fin m) := by
  classical
  rw [LatticeGoodness.mem_stdLat]
  intro j
  have h0 : (Pi.single j 1 : Fin m → Ω) ∈ stdLat R (Fin m) := by
    rw [LatticeGoodness.mem_stdLat]
    intro k
    by_cases hk : k = j
    · subst hk; simpa using R.one_mem
    · simpa [Pi.single_apply, hk] using R.zero_mem
  have h1 : w • (Pi.single j 1 : Fin m → Ω) ∈ A := h (AddSubgroup.mem_map.2 ⟨_, h0, rfl⟩)
  have h2 := (mem_dotDual_iff R).1 hv _ h1
  simpa [smul_dotProduct] using h2

theorem core (R : Subalgebra o Ω) {a b c : ℕ} (W : AddSubgroup (Fin a → Ω))
    (O : AddSubgroup (Fin c → Ω)) (Gam : AddSubgroup ((Fin a → Ω) × (Fin b → Ω)))
    (Del : AddSubgroup ((Fin b → Ω) × (Fin c → Ω))) (H : AddSubgroup (Fin b → Ω)) (w : Ω)
    (hw0 : w ≠ 0) (fW : LocFree R a W) (fO : LocFree R c O) (fH : LocFree R b H)
    (hstd : stdLat R (Fin b) ≤ H) (hwv : ∀ v ∈ H, w • v ∈ stdLat R (Fin b))
    (fIm : LocFree R c ((Del ⊓ H.prod ⊤).map (AddMonoidHom.snd _ _)))
    (sG : ∀ x ∈ R, ∀ v ∈ Gam, x • v ∈ Gam) (sD : ∀ x ∈ R, ∀ v ∈ Del, x • v ∈ Del)
    (g1 : ∀ x, (∃ y, (x, y) ∈ Gam) ↔ w • x ∈ W) (g2 : ∀ y, (0, y) ∈ Gam ↔ y ∈ stdLat R _)
    (g3 : ∀ x, (x, 0) ∈ Gam ↔ x ∈ W)
    (d1 : ∀ y, (∃ z, (y, z) ∈ Del) ↔ w • y ∈ stdLat R _) (d3 : ∀ z, (0, z) ∈ Del ↔ z ∈ O)
    (d4 : ∀ y, (y, 0) ∈ Del ↔ ∃ x, (x, y) ∈ Gam) :
    LocFree R a ((Gam ⊓ (⊤ : AddSubgroup _).prod H).map (AddMonoidHom.fst _ _)) := by

  have hK : LocFree R b ((Del ⊓ H.prod ⊤).comap (AddMonoidHom.inl _ _)) := by
    refine (LocFreeSchanuel.main R b c H _ O (Del ⊓ H.prod ⊤) fH fIm fO ?_ ?_ ?_ ?_ ?_).2
    · intro x hx v hv
      obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hv
      refine AddSubgroup.mem_inf.2 ⟨sD x hx v h1, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩
      exact fH.1 x hx _ (AddSubgroup.mem_prod.1 h2).1
    · intro v z h
      exact ⟨(AddSubgroup.mem_prod.1 (AddSubgroup.mem_inf.1 h).2).1, AddSubgroup.mem_map.2 ⟨(v, z), h, rfl⟩⟩
    · intro v hv
      obtain ⟨z, hz⟩ := (d1 v).2 (hwv v hv)
      exact ⟨z, AddSubgroup.mem_inf.2 ⟨hz, AddSubgroup.mem_prod.2 ⟨hv, trivial⟩⟩⟩
    · intro z
      constructor
      · intro h
        exact (d3 z).1 (AddSubgroup.mem_inf.1 h).1
      · intro h
        exact AddSubgroup.mem_inf.2 ⟨(d3 z).2 h, AddSubgroup.mem_prod.2 ⟨H.zero_mem, trivial⟩⟩
    · intro z hz
      obtain ⟨⟨v, z'⟩, h, rfl⟩ := AddSubgroup.mem_map.1 hz
      exact ⟨v, h⟩
  have sG' : ∀ x ∈ R, ∀ v ∈ Gam ⊓ (⊤ : AddSubgroup _).prod H, x • v ∈ Gam ⊓ (⊤ : AddSubgroup _).prod H := by
    intro x hx v hv
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hv
    exact AddSubgroup.mem_inf.2 ⟨sG x hx v h1, AddSubgroup.mem_prod.2
      ⟨trivial, fH.1 x hx _ (AddSubgroup.mem_prod.1 h2).2⟩⟩

  have hG' : LocFree R (a + b) (Gam ⊓ (⊤ : AddSubgroup _).prod H) := by
    have e1 : (Gam ⊓ (⊤ : AddSubgroup _).prod H).comap
        (LinearMap.inl Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = W := by
      ext x
      constructor
      · intro h
        exact (g3 x).1 (AddSubgroup.mem_inf.1 h).1
      · intro h
        exact AddSubgroup.mem_inf.2 ⟨(g3 x).2 h, AddSubgroup.mem_prod.2 ⟨trivial, H.zero_mem⟩⟩
    have e2 : (Gam ⊓ (⊤ : AddSubgroup _).prod H).map
        (LinearMap.snd Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom =
        (Del ⊓ H.prod ⊤).comap (AddMonoidHom.inl _ _) := by
      ext y
      constructor
      · intro h
        obtain ⟨⟨x, y'⟩, hxy, rfl⟩ := AddSubgroup.mem_map.1 h
        obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hxy
        exact AddSubgroup.mem_inf.2 ⟨(d4 y').2 ⟨x, h1⟩,
          AddSubgroup.mem_prod.2 ⟨(AddSubgroup.mem_prod.1 h2).2, trivial⟩⟩
      · intro h
        obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 h
        obtain ⟨x, hx⟩ := (d4 y).1 h1
        exact AddSubgroup.mem_map.2 ⟨(x, y), AddSubgroup.mem_inf.2 ⟨hx,
          AddSubgroup.mem_prod.2 ⟨trivial, (AddSubgroup.mem_prod.1 h2).1⟩⟩, rfl⟩
    exact LocFreeExt.main R (LinearMap.inl Ω _ _) (LinearMap.snd Ω _ _) LinearMap.inl_injective
      LinearMap.snd_surjective (LinearMap.range_inl Ω _ _) _ a b sG' (e1 ▸ fW) (e2 ▸ hK)

  have eF : Gam.map (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = divLat w W := by
    ext x
    constructor
    · intro h
      obtain ⟨⟨x', y⟩, hxy, rfl⟩ := AddSubgroup.mem_map.1 h
      exact (g1 x').1 ⟨y, hxy⟩
    · intro h
      obtain ⟨y, hy⟩ := (g1 x).2 h
      exact AddSubgroup.mem_map.2 ⟨(x, y), hy, rfl⟩
  have fDiv : LocFree R a (Gam.map (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom) :=
    eF ▸ LatticeGoodness.locFree_divLat R hw0 fW
  have hGam : LocFree R (b + a) Gam := by
    have e1 : Gam.comap (LinearMap.inr Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = stdLat R (Fin b) := by
      ext y
      exact g2 y
    exact LocFreeExt.main R (LinearMap.inr Ω _ _) (LinearMap.fst Ω _ _) LinearMap.inr_injective
      LinearMap.fst_surjective (LinearMap.range_inr Ω _ _) _ b a sG
      (e1 ▸ LatticeGoodness.locFree_stdLat R b) fDiv

  have hfin : Module.finrank Ω (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω))) = b := by
    rw [← LinearMap.range_inr, LinearMap.finrank_range_of_inj LinearMap.inr_injective,
      Module.finrank_fin_fun]
  obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := (GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)))
    (b + a) a Gam hGam).1
    ((LatticeGoodness.locFree_map_mkQ_iff R _ LinearMap.fst_surjective Gam).2 fDiv)
  have hS : Summand (Gam ⊓ (⊤ : AddSubgroup _).prod H)
      (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω))) := by
    refine ⟨ρ, hρ1, hρ2, fun v hv => ?_⟩
    have h1 := hρ3 v (AddSubgroup.mem_inf.1 hv).1
    have h2 : (ρ v).1 = 0 := hρ1 v
    refine AddSubgroup.mem_inf.2 ⟨h1, AddSubgroup.mem_prod.2 ⟨trivial, hstd ?_⟩⟩
    apply (g2 _).1
    have : ((0 : Fin a → Ω), (ρ v).2) = ρ v := by rw [← h2]
    rwa [this]
  have hfinal := ((GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)))
    (a + b) a _ hG').2 hS).2
  rw [hfin, Nat.add_sub_cancel] at hfinal
  exact (LatticeGoodness.locFree_map_mkQ_iff R _ LinearMap.fst_surjective _).1 hfinal

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hC hB hG₁ hG₂ hw τ
  have hw0 : w ≠ 0 := by
    obtain ⟨c, -, hc⟩ := hC.2.2.1
    intro h
    apply hC.1
    rw [hc, h, mul_zero]
  obtain ⟨-, fH, hle, -⟩ := (GlobalTheory.T.lattice_good_base_change D R p w χ hC hB hG₁).1 τ
  obtain ⟨-, fW, -, fO⟩ := hB.free τ
  obtain ⟨g1, g2, g3⟩ := hB.gam τ
  obtain ⟨d1, -, d3, d4⟩ := hB.del τ
  exact core R (D.W τ) (D.omHT τ) (D.Gam τ) (D.Del τ) (D.hh R p (χ τ)) w hw0 fW fO fH
    (std_le_dual R hle) (fun v hv => smul_mem_std R (hw τ) hv) (hG₂.im τ)
    (fun x hx => (hB.stable τ x hx).1) (fun x hx => (hB.stable τ x hx).2.1) g1 g2 g3 d1 d3 d4

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree
