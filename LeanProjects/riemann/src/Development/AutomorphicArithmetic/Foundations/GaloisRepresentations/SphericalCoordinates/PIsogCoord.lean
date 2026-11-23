import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresChangeOfForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdeleStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.IsogenyReduction

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private theorem exists_bound (k : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) :
    ∃ c : ℕ, 0 < c ∧ ∀ z ∈ LaHat D, c • k z ∈ LaHat D := by
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let S : Set (AfP p) := Set.range (fun ij : Module.Free.ChooseBasisIndex ℤ D.La × Module.Free.ChooseBasisIndex ℤ D.La =>
    (KNLevel.bA b).repr (k (KNLevel.bA b ij.2)) ij.1)
  have hS : IsCompact S := (Set.finite_range _).isCompact
  obtain ⟨c, hc, hcS⟩ := GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway p S hS
  refine ⟨c, hc, ?_⟩
  have hB : ∀ j, inAf D (b j) = KNLevel.bA b j := by
    intro j
    simp [KNLevel.bA, inAf, Algebra.TensorProduct.basis_apply]
  have hgen : ∀ j, c • k (inAf D (b j)) ∈ LaHat D := by
    intro j
    apply KNLevel.mem_laHat_of_repr b
    intro i
    rw [hB j, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    exact hcS _ ⟨(i, j), rfl⟩
  have hall : ∀ x : D.La, (c • k) (inAf D x) ∈ LaHat D := by
    intro x
    let f : D.La →+ (AfP p ⊗[ℚ] VQ D) :=
      ((c • k).toAddMonoidHom).comp (AddMonoidHom.mk' (inAf D) GammaUniq.inAf_add)
    have hf : ∀ y, f y = (c • k) (inAf D y) := fun y => rfl
    rw [← hf, ← b.sum_repr x, map_sum]
    refine AddSubgroup.sum_mem _ (fun j _ => ?_)
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (hgen j) _
  intro z hz
  exact GammaUniq.map_mem (c • k) hall hz

private theorem end_eq (k T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
    (h : ∀ (a : D.La) (n : ℕ), 0 < n → n.Coprime p → ∃ w ∈ LaHat D, ∃ w' ∈ LaHat D,
      k (inAf D a) = T (inAf D a) + n • w + n • k w') : k = T := by
  apply GammaUniq.end_ext
  intro a
  obtain ⟨c, hc, hcb⟩ := exists_bound k
  have hz : c • (k (inAf D a) - T (inAf D a)) = 0 := by
    apply GammaUniq.eq_zero_of_dvd_laHat
    intro n hn hnp
    obtain ⟨w, hw, w', hw', he⟩ := h a n hn hnp
    refine ⟨c • w + c • k w', add_mem (AddSubgroup.nsmul_mem _ hw c) (hcb w' hw'), ?_⟩
    have hd : k (inAf D a) - T (inAf D a) = n • w + n • k w' := by
      rw [he]
      abel
    rw [hd, smul_add, smul_add, smul_comm c n w, smul_comm c n (k w')]
  have hX : k (inAf D a) - T (inAf D a) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℚ] at hz
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hc.ne')
  exact sub_eq_zero.mp hX

variable (L : Link D G)

private theorem rd_add (x : (AfP p ⊗[ℚ] G.C)ˣ) (g : G.GAf) (u w : VQ D) :
    rd L x g (u + w) = rd L x g u + rd L x g w := by
  simp only [rd, TensorProduct.tmul_add, map_add]

private theorem rd_nsmul (x : (AfP p ⊗[ℚ] G.C)ˣ) (g : G.GAf) (n : ℕ) (w : VQ D) :
    rd L x g (n • w) = n • rd L x g w := by
  induction n with
  | zero =>
    simp only [zero_smul, UpperTheory.Gal.W2.rd, TensorProduct.tmul_zero, map_zero]
  | succ n ih =>
    rw [succ_nsmul, rd_add, ih, succ_nsmul]

private theorem rd_eq (x : (AfP p ⊗[ℚ] G.C)ˣ) (g h : G.GAf) (w : VQ D) :
    rd L x h w = L.actG (h⁻¹ * g) (rd L x g w) := by
  unfold UpperTheory.Gal.W2.rd
  rw [← Module.End.mul_apply (L.actG (h⁻¹ * g)), ← map_mul, mul_inv_cancel_right]

private theorem coord_of (x : (AfP p ⊗[ℚ] G.C)ˣ) {N : ℕ} {D' : PLat D.O D.inv} {t t₀ : D.La → D'.La}
    {j : D'.La →+ VQ D} {g : G.GAf} (hc : IsCoordA L x N D' t₀ j g) (h : ∀ a, ∃ u, t₀ a = t a + N • u) :
    IsCoordA L x N D' t j g := by
  refine ⟨hc.1, fun a => ?_⟩
  obtain ⟨w, hw, he⟩ := hc.2 a
  obtain ⟨u, hu⟩ := h a
  have hmem : rd L x g (j u) ∈ LaHat D := (hc.1 (j u)).mp ⟨0, u, by simp⟩
  refine ⟨w - rd L x g (j u), sub_mem hw hmem, ?_⟩
  rw [hu, map_add, map_nsmul, rd_add, rd_nsmul] at he
  rw [smul_sub, ← add_sub_assoc, ← he, add_sub_cancel_right]

end UpperTheory.Gal.W2.IsogenyReduction

open UpperTheory.Gal.W2.IsogenyReduction in
theorem UpperTheory.Gal.W2.isogCoord_of :
    UpperTheory.Gal.W2.AdOfWit → UpperTheory.Gal.W2.CoordKN → UpperTheory.Gal.W2.IsogForm → UpperTheory.Gal.W2.RdDense → UpperTheory.Gal.W2.IsogCoord := by
  intro hAd hCo hIf hRd p _ D G L B N N' hN hNp hN' hN'p h hconj ρ D' t D'' t'' P P'' inc d hP hP'' hPP
    hdp hd f nu f'' nu'' hf hf'' hft hft'' hiff j h₁ M hpl hco hloc
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hdp)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hinc : Function.Injective inc := fun u1 u2 he => hP.2.1 (by rw [← hPP u1, ← hPP u2, he])
  obtain ⟨lift, hlift⟩ : ∃ lift : D''.La → D'.La, ∀ u'', inc (lift u'') = d • u'' :=
    ⟨fun u'' => (hd u'').choose, fun u'' => (hd u'').choose_spec⟩
  have hlift_add : ∀ a b, lift (a + b) = lift a + lift b := fun a b =>
    hinc (by rw [map_add, hlift, hlift, hlift, smul_add])
  have hlift_inc : ∀ u, lift (inc u) = d • u := fun u => hinc (by rw [hlift, map_nsmul])
  obtain ⟨j'', hj''⟩ : ∃ j'' : D''.La →+ VQ D, ∀ u'', j'' u'' = (d : ℚ)⁻¹ • j (lift u'') :=
    ⟨AddMonoidHom.mk' (fun u'' => (d : ℚ)⁻¹ • j (lift u''))
      (fun a b => by simp only [hlift_add, map_add, smul_add]), fun _ => rfl⟩
  have hj''d : ∀ u'', (d : ℚ) • j'' u'' = j (lift u'') := by
    intro u''
    rw [hj'', smul_smul, mul_inv_cancel₀ hd', one_smul]
  have hj''inc : ∀ u, j'' (inc u) = j u := by
    intro u
    rw [hj'', hlift_inc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hd', one_smul]
  have hpl'' : IsPlace L B.β D'' j'' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      have h1 : j (lift a) = j (lift b) := by rw [← hj''d, ← hj''d, hab]
      have h2 := hpl.1 h1
      have h3 : d • a = d • b := by rw [← hlift, ← hlift, h2]
      haveI := D''.free
      have h4 : (d : ℤ) • a = (d : ℤ) • b := by rw [natCast_zsmul, natCast_zsmul]; exact h3
      exact smul_right_injective D''.La (by exact_mod_cast hd0 : (d : ℤ) ≠ 0) h4
    · intro c u
      have hl : lift (c • u) = c • lift u := hinc (by
        rw [hlift, map_smul, hlift]
        exact smul_comm d c u)
      rw [hj'', hj'', hl, hpl.2.1, map_smul]
    · intro w
      obtain ⟨m, u, hm, hmw⟩ := hpl.2.2.1 w
      exact ⟨m, inc u, hm, by rw [hj''inc]; exact hmw⟩
    · obtain ⟨r, hr, hrEF⟩ := hIf p D G L h ρ D' D'' P P'' inc hP hP'' hPP f nu f'' nu'' hf hf'' hiff
      obtain ⟨s, hs, hsEF⟩ := hpl.2.2.2
      refine ⟨r * s, mul_pos hr hs, fun u1 u2 => ?_⟩
      have key : ((D''.EF (d • u1) (d • u2) : ℤ) : ℚ) = (d : ℚ) * d * (D''.EF u1 u2) := by
        simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
        push_cast
        ring
      have hform : ∀ (c : ℚ) (x y : VQ D), formB L B.β (c • x) (c • y) = c * c * formB L B.β x y := by
        intro c x y
        simp only [formB, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      calc ((D''.EF u1 u2 : ℤ) : ℚ) = ((d : ℚ) * d)⁻¹ * (D''.EF (d • u1) (d • u2) : ℤ) := by
            rw [key]
            field_simp
        _ = ((d : ℚ) * d)⁻¹ * (D''.EF (inc (lift u1)) (inc (lift u2)) : ℤ) := by rw [hlift, hlift]
        _ = ((d : ℚ) * d)⁻¹ * (r * (D'.EF (lift u1) (lift u2) : ℤ)) := by rw [hrEF]
        _ = ((d : ℚ) * d)⁻¹ * (r * (s * formB L B.β (j (lift u1)) (j (lift u2)))) := by rw [hsEF]
        _ = r * s * formB L B.β (j'' u1) (j'' u2) := by
            rw [← hj''d u1, ← hj''d u2, hform]
            field_simp
  have hloc'' : IsLocP D'' j'' M := by
    intro w
    constructor
    · rintro ⟨m, u'', hm, hmw⟩
      refine (hloc w).mp ⟨d * m, lift u'', Nat.Coprime.mul hdp hm, ?_⟩
      rw [mul_smul, hmw, ← hj''d, Nat.cast_smul_eq_nsmul]
    · intro hw
      obtain ⟨m, u, hm, hmw⟩ := (hloc w).mpr hw
      exact ⟨m, inc u, hm, by rw [hj''inc]; exact hmw⟩
  obtain ⟨h₂, hR₂⟩ := hAd p D G L B D'' j'' hpl'' f'' nu'' hf''
  obtain ⟨h₃, hR₃⟩ := hAd p D G L B D' j hpl f nu hf
  have hc₂ : IsCoordA L (trivX B) N D'' t'' j'' h₂ := coord_of L (trivX B) (hR₂ N hN hNp) hft''
  have hc₃ : IsCoordA L (trivX B) N' D' t j h₃ := coord_of L (trivX B) (hR₃ N' hN' hN'p) hft
  have hk₃ : h₃⁻¹ * h₁ ∈ L.KN N' := (hCo p D G L (trivX B) N' hN' hN'p D' t j h₁ h₃ hco).mp hc₃
  have hkey : h₂⁻¹ * h₃ = h := by
    apply GammaUniq.actG_injective L
    apply end_eq
    intro a n hn hnp
    obtain ⟨w₃, hw₃m, hw₃⟩ := (hR₃ n hn hnp).2 a
    obtain ⟨b, e, he⟩ := (hf''.2 n hn hnp).2.2.2.1 (inc (f n a))
    obtain ⟨wT, hwTm, hT⟩ := (hiff n hn hnp a b).mp ⟨e, he⟩
    obtain ⟨w₂, hw₂m, hw₂⟩ := (hR₂ n hn hnp).2 b
    have hrm : rd L (trivX B) h₂ (j'' e) ∈ LaHat D := ((hR₂ n hn hnp).1 (j'' e)).mp ⟨0, e, by simp⟩
    refine ⟨w₂ + rd L (trivX B) h₂ (j'' e) - wT, sub_mem (add_mem hw₂m hrm) hwTm, -w₃, neg_mem hw₃m, ?_⟩
    have eA : rd L (trivX B) h₂ (j (f n a)) = L.actG (h₂⁻¹ * h₃) (inAf D a) + n • L.actG (h₂⁻¹ * h₃) w₃ := by
      rw [rd_eq L (trivX B) h₃ h₂, hw₃, map_add, map_nsmul]
    have eB : rd L (trivX B) h₂ (j (f n a)) = inAf D b + n • w₂ + n • rd L (trivX B) h₂ (j'' e) := by
      rw [← hj''inc, he, map_add, map_nsmul, rd_add, rd_nsmul, hw₂]
    have e1 := eA.symm.trans eB
    rw [eq_sub_of_add_eq e1, hT]
    simp only [smul_add, smul_sub, map_neg, smul_neg]
    abel
  have hh₂ : h₂ = h₃ * h⁻¹ := by
    rw [← hkey, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  refine ⟨j'', hj''inc, hpl'', ?_, hloc''⟩
  apply (hCo p D G L (trivX B) N hN hNp D'' t'' j'' h₂ (h₁ * h⁻¹) hc₂).mpr
  have hx : (h₁ * h⁻¹)⁻¹ * h₂ = h * (h₃⁻¹ * h₁)⁻¹ * h⁻¹ := by
    rw [hh₂]
    group
  rw [hx]
  exact hconj _ (inv_mem hk₃)
