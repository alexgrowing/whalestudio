import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_KN_inv_mul_mem_inf_map_conj
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)) :
    IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∀ y ∈ J,
      ∃ a ∈ KN k N J d hd, a⁻¹ * y ∈
        J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  intro _ _ hfact _ t hdom y hy
  obtain ⟨-, hNl, hM⟩ := hdom
  obtain ⟨u, hu, b, hb, n, hn, hyf⟩ := hfact y⁻¹ (J.inv_mem hy)
  obtain ⟨huJ, -⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hbJ, x, rfl⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hnJ, hnN⟩ := Subgroup.mem_inf.1 hn
  have hy' : y = n⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * u⁻¹ := by
    have : y = (y⁻¹)⁻¹ := (inv_inv y).symm
    rw [this, hyf]; group
  refine ⟨n⁻¹, (KN k N J d hd).inv_mem (Subgroup.mem_inf.2 ⟨hnJ, hnN⟩), ?_⟩
  have hred : (n⁻¹)⁻¹ * y = (leviEmb k (stdBlocks d hd) x)⁻¹ * u⁻¹ := by
    rw [hy']; group
  rw [hred]
  set g := leviEmb k (stdBlocks d hd) t with hg
  have hxKM : x⁻¹ ∈ KM k N J d hd :=
    (KM k N J d hd).inv_mem (show x ∈ (J).comap (leviEmb k (stdBlocks d hd)) from hbJ)
  have h1 : g⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * g ∈ J := by
    have h2 : t⁻¹ * x⁻¹ * t ∈ KM k N J d hd := (hM _ hxKM).2
    have h3 : leviEmb k (stdBlocks d hd) (t⁻¹ * x⁻¹ * t) ∈ J := h2
    simpa [hg, map_mul, map_inv] using h3
  have h4 : g⁻¹ * u⁻¹ * g ∈ J :=
    (Subgroup.mem_inf.1 (hNl _ ((KNl k N J d hd).inv_mem hu))).1
  refine Subgroup.mem_inf.2 ⟨J.mul_mem (J.inv_mem hbJ) (J.inv_mem huJ), ?_⟩
  refine Subgroup.mem_map.2 ⟨(g⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * g) * (g⁻¹ * u⁻¹ * g),
    J.mul_mem h1 h4, ?_⟩
  simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end GlobalTheory.CompanionTheory.Casselman
