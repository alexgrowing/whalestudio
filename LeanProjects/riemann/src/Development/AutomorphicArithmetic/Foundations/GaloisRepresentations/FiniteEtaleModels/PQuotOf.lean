import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem conj_congOne {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {u v : G.GAf} {N : ℕ}
    (hu : u ∈ L.KN 1) (hv : L.CongOne N v) : L.CongOne N (u * v * u⁻¹) := by
  intro z hz
  have hu' : L.CongOne 1 u ∧ L.CongOne 1 u⁻¹ := hu
  obtain ⟨w1, hw1, e1⟩ := hu'.2 z hz
  have hz' : L.actG u⁻¹ z ∈ LaHat D := by
    rw [e1, one_smul]
    exact add_mem hz hw1
  obtain ⟨w2, hw2, e2⟩ := hv _ hz'
  obtain ⟨w3, hw3, e3⟩ := hu'.1 w2 hw2
  refine ⟨L.actG u w2, ?_, ?_⟩
  · rw [e3, one_smul]
    exact add_mem hw2 hw3
  · have key : L.actG u (L.actG u⁻¹ z) = z := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, map_add, map_nsmul, key]

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

private theorem cl_cast {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E]
    {gb : GBase D.toG E} {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)}
    (S : Site gb w q r 𝔴 𝔫) {k : ℕ} (T : KS L gb k) (M : Lv p) {c c' : ℕ} {a a' : 𝓞 D.F} (hc : c' = c) (ha : a' = a)
    (C : S.Cl (T.M M).univ c a) : ∃ C' : S.Cl (T.M M).univ c' a', S.pi T C' = S.pi T C := by
  subst hc ha
  exact ⟨C, rfl⟩

theorem UpperTheory.Gal.FiniteEtaleModels.quotOf_holds :
    PowCart → PiInv → PiFet → PiSep → CongCRT → BaseOnto → QuotOf := by
  intro hPC hPI hPF hPS hCRT hBO p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK M c a hNum C
  have hM := hNum.1
  have hGen := hNum.2
  let N0 : Lv p := ⟨S.N₀, S.std.three, S.cop⟩
  have hMpos : 0 < M.1 := by have := M.2.1; omega
  have hdvd : S.N₀ ∣ M.1 := ⟨c, hM⟩
  have hup := S.upow
  have hcop : S.N₀.Coprime q := S.std.cop
  have hK₀le : K₀ ≤ L.KN S.N₀ := by
    have key : ∀ g, g ∈ K₀ → L.CongOne S.N₀ g := fun g hg => by
      have h := (hK g).1 hg
      have h2 := h.2
      rw [S.lev] at h2
      exact (((hCRT p D G L q r S.N₀ S.𝔞 hcop hup g (integ_of_mem h.1)).1).1 h2).1
    exact fun g hg => ⟨key g hg, key _ (inv_mem hg)⟩
  have hKM : L.KN M.1 ≤ K₀ := by
    intro g hg
    have h1 : g ∈ L.KN 1 := KN_anti (one_dvd _) hg
    have hcrt := hCRT p D G L q r S.N₀ S.𝔞 hcop hup g (integ_of_mem h1)
    have h2 : L.CongOne S.N₀ g := (KN_anti hdvd hg).1
    have h3 : CongId L S.𝔞 g := (hcrt.2 a M.1 hMpos M.2.2 hGen).2 fun y => hg.1 _ (inAf_mem' D _)
    exact (hK g).2 ⟨h1, by rw [S.lev]; exact hcrt.1.2 ⟨h2, h3⟩⟩
  have hX : T.X.K (T.lev M) = L.KN M.1 := T.K_eq M
  have hX0 : T.X.K (T.lev N0) = L.KN S.N₀ := T.K_eq N0
  refine ⟨?ov, ?le, ?idx, ?adm, ?inv, ?fib, ?free, ?onto⟩
  · obtain ⟨e, -⟩ := hPF p D G L E gb w q r 𝔴 𝔫 S k T M c a hNum C
    exact e
  · rw [hX]; exact hKM
  · rw [hX]
    have h := T.X.idx (T.lev M) (T.lev N0)
    rw [hX, hX0] at h
    exact fun e => h (Subgroup.relIndex_eq_zero_of_le_right hK₀le e)
  · intro u hu
    have hu1 := ((hK u).1 hu).1
    refine ⟨(T.Δ_eq u).2 (integ_of_mem hu1), fun v hv => ?_⟩
    rw [hX] at hv ⊢
    refine ⟨conj_congOne L hu1 hv.1, ?_⟩
    have e : (u * v * u⁻¹)⁻¹ = u * v⁻¹ * u⁻¹ := by group
    rw [e]; exact conj_congOne L hu1 hv.2
  · intro u hu x y
    obtain ⟨C', hC'⟩ := cl_cast (a' := ((1 : ℕ) : 𝓞 D.F) * a) S T M (_root_.mul_one c) (by simp) C
    have h := hPI p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK M M 1 c a (_root_.mul_one _).symm hNum C' C u hu x y
    rwa [hC'] at h
  · intro Ω _ _ x y h
    exact hPS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK M c a hNum C Ω x y h
  · intro u hu x y Ω _ _ z hz
    exact T.X.free _ (T.lev N0) (by rw [hX, hX0]; exact KN_anti hdvd) u (by rw [hX0]; exact hK₀le hu) x y Ω z hz
  · intro Ω _ _ y σ hy
    obtain ⟨x₀, hx₀, -⟩ := hBO p D G L hSc E gb w q r 𝔴 𝔫 S k T M c a hNum C Ω (y ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom) σ
      (by simpa using hy)
    have hpb := (hPC _ _ _ (T.M M).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) C.m.cart.1.w (by simp) k).1 C.m.cart.1
    refine ⟨hpb.lift y x₀ hx₀.symm ≫ (T.e M).inv, ?_⟩
    simp only [Site.pi, Cls.pw, Category.assoc, Iso.inv_hom_id_assoc]
    exact hpb.lift_fst _ _ _
