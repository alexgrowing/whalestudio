import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.LatticeIsomorphism

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem rd_add (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (u v : VQ D) :
    rd L x h (u + v) = rd L x h u + rd L x h v := by
  simp only [rd, TensorProduct.tmul_add, map_add]

private noncomputable def rdHom (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) : VQ D →+ AfP p ⊗[ℚ] VQ D :=
  AddMonoidHom.mk' (rd L x h) (rd_add L x h)

private theorem rd_sub (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (u v : VQ D) :
    rd L x h (u - v) = rd L x h u - rd L x h v := by
  exact map_sub (rdHom L x h) u v

private theorem rd_nsmul (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (n : ℕ) (u : VQ D) :
    rd L x h (n • u) = n • rd L x h u := by
  exact map_nsmul (rdHom L x h) n u

private theorem actY_inv {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y (actY L y⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem inv_actY {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y⁻¹ (actY L y w) = w := by
  show L.rep ((y⁻¹ : GlobalTheory.LKCx.grp G β) : G.Cˣ × ℚˣ).1 (L.rep ((y : G.Cˣ × ℚˣ).1 : G.C) w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private noncomputable def placeY {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv} (j'' : D''.La →+ VQ D) :
    D''.La →+ VQ D :=
  (LinearMap.toAddMonoidHom (actY L y)).comp j''

private theorem placeY_apply {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv} (j'' : D''.La →+ VQ D)
    (u : D''.La) : placeY L y j'' u = actY L y (j'' u) := rfl

private theorem coordA_placeY (hR : RdAct) (B : GlobalTheory.LKCx.Form G) (y : GlobalTheory.LKCx.grp G B.β) {N : ℕ}
    {D'' : PLat D.O D.inv} {t'' : D.La → D''.La} {j'' : D''.La →+ VQ D} {h : G.GAf}
    (hc : IsCoordA L (trivX B) N D'' t'' j'' h) :
    IsCoordA L (trivX B) N D'' t'' (placeY L y j'') (B.toAf y * h) := by
  have key : ∀ w, rd L (trivX B) (B.toAf y * h) (actY L y w) = rd L (trivX B) h w := by
    intro w
    rw [hR p D G L B y (B.toAf y * h) h w]
    have e : (B.toAf y * h)⁻¹ * B.toAf y * h = 1 := by group
    rw [e, map_one, Module.End.one_apply]
  refine ⟨fun w => ?_, fun a => ?_⟩
  · have hw : w = actY L y (actY L y⁻¹ w) := (actY_inv L y w).symm
    rw [hw, key, ← hc.1 (actY L y⁻¹ w), ← hw]
    constructor
    · rintro ⟨r, u, hu⟩
      refine ⟨r, u, ?_⟩
      rw [placeY_apply] at hu
      rw [← map_nsmul, hu, inv_actY]
    · rintro ⟨r, u, hu⟩
      refine ⟨r, u, ?_⟩
      rw [placeY_apply, ← hu, map_nsmul, actY_inv]
  · obtain ⟨w1, hw1, e⟩ := hc.2 a
    exact ⟨w1, hw1, by rw [placeY_apply, key, e]⟩

private theorem locP_placeY {β : G.Cˣ} (PD : PDic L β) (y : GlobalTheory.LKCx.grp G β) {D'' : PLat D.O D.inv}
    {j'' : D''.La →+ VQ D} {hp : Gr G 1} (hl : IsLocP D'' j'' (PD.lat hp)) :
    IsLocP D'' (placeY L y j'') (PD.lat (GlobalTheory.LKCx.toP1 G β y * hp)) := by
  intro w
  have hw : w = actY L y (actY L y⁻¹ w) := (actY_inv L y w).symm
  rw [hw, PD.equiv y hp, ← hl (actY L y⁻¹ w), ← hw]
  constructor
  · rintro ⟨m, u, hm, hu⟩
    refine ⟨m, u, hm, ?_⟩
    rw [placeY_apply] at hu
    rw [← map_nsmul, hu, inv_actY]
  · rintro ⟨m, u, hm, hu⟩
    refine ⟨m, u, hm, ?_⟩
    rw [placeY_apply, ← hu, map_nsmul, actY_inv]

private theorem range_le {x : (AfP p ⊗[ℚ] G.C)ˣ} {N : ℕ} {D₁ D₂ : PLat D.O D.inv} {t₁ : D.La → D₁.La}
    {t₂ : D.La → D₂.La} {j₁ : D₁.La →+ VQ D} {j₂ : D₂.La →+ VQ D} {h : G.GAf} {M : AddSubgroup (VQ D)}
    (hc₁ : IsCoordA L x N D₁ t₁ j₁ h) (hc₂ : IsCoordA L x N D₂ t₂ j₂ h)
    (hl₁ : IsLocP D₁ j₁ M) (hl₂ : IsLocP D₂ j₂ M) (u : D₁.La) : ∃ u₂, j₂ u₂ = j₁ u := by
  obtain ⟨r, u₂, hu₂⟩ := (hc₂.1 (j₁ u)).2 ((hc₁.1 (j₁ u)).1 ⟨0, u, by simp⟩)
  obtain ⟨m, u₃, hm, hu₃⟩ := (hl₂ (j₁ u)).2 ((hl₁ (j₁ u)).1 ⟨1, u, Nat.coprime_one_left p, one_smul _ _⟩)
  have hcop : IsCoprime ((p ^ r : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left r hm.symm)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • u₂ + b • u₃, ?_⟩
  calc j₂ (a • u₂ + b • u₃) = a • j₂ u₂ + b • j₂ u₃ := by rw [map_add, map_zsmul, map_zsmul]
    _ = (a * ((p ^ r : ℕ) : ℤ) + b * (m : ℤ)) • j₁ u := by
      rw [← hu₂, ← hu₃, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
    _ = j₁ u := by rw [hab, one_smul]

private theorem mark_div {x : (AfP p ⊗[ℚ] G.C)ˣ} {N : ℕ} (hN0 : 0 < N) (hNp : N.Coprime p) {D₁ : PLat D.O D.inv}
    {j : D₁.La →+ VQ D} (hj : Function.Injective j) {h : G.GAf}
    (hc : ∀ w, (∃ (r : ℕ) (u : D₁.La), p ^ r • w = j u) ↔ rd L x h w ∈ LaHat D)
    (d : D₁.La) {w₃ : AfP p ⊗[ℚ] VQ D} (hw₃ : w₃ ∈ LaHat D) (hd : rd L x h (j d) = N • w₃) :
    ∃ e : D₁.La, d = N • e := by
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
  set w : VQ D := (N : ℚ)⁻¹ • j d with hwdef
  have hNw : N • w = j d := by
    rw [hwdef, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hN, one_smul]
  have e : rd L x h w = w₃ := by
    have h1 : (N : ℚ) • rd L x h w = (N : ℚ) • w₃ := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← rd_nsmul, hNw, hd]
    have h2 := congrArg (fun z => (N : ℚ)⁻¹ • z) h1
    simpa only [smul_smul, inv_mul_cancel₀ hN, one_smul] using h2
  obtain ⟨r, u, hu⟩ := (hc w).2 (e ▸ hw₃)
  have h3 : j (p ^ r • d) = j (N • u) := by
    rw [map_nsmul, map_nsmul, ← hNw, ← hu, smul_comm]
  have h4 := hj h3
  have hcop : IsCoprime (N : ℤ) ((p ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right r hNp)
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • d + b • u, ?_⟩
  calc d = (a * (N : ℤ) + b * ((p ^ r : ℕ) : ℤ)) • d := by rw [hab, one_smul]
    _ = N • (a • d + b • u) := by
      rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, h4, smul_add, smul_comm N a d,
        smul_comm N b u]

end UpperTheory.Gal.W2.LatticeIsomorphism

open UpperTheory.Gal.W2.LatticeIsomorphism

theorem UpperTheory.Gal.W2.latIso_of :
    UpperTheory.Gal.W2.RdAct → UpperTheory.Gal.W2.CoordKN → UpperTheory.Gal.W2.ClsScalar → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.LatIso := by
  intro hR hK hS hA p _ D G L B PD N hN hNp D' t D'' t'' j j'' a a'' N₁ N₂ t₁ t₂ hc₁ hc₂ hpl hpl'' hca hca''
    hlp hlp'' y
  have hcaY : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') (B.toAf y * a''.1) := coordA_placeY L hR B y hca''
  have hlpY : IsLocP D'' (placeY L y j'') (PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2)) := locP_placeY L PD y hlp''
  constructor
  · rintro ⟨hm1, hm2⟩
    have hcaY' : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') a.1 :=
      (hK p D G L (trivX B) N hN hNp D'' t'' (placeY L y j'') _ _ hcaY).2 (by rwa [← _root_.mul_assoc])
    have hlat : PD.lat a.2 = PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2) :=
      (PD.inj _ _).2 (by rwa [← _root_.mul_assoc])
    have hlpY' : IsLocP D'' (placeY L y j'') (PD.lat a.2) := by
      rw [hlat]
      exact hlpY
    have hex : ∀ u : D''.La, ∃ u', j u' = placeY L y j'' u := range_le L hcaY' hca hlpY' hlp
    have hex' : ∀ u' : D'.La, ∃ u, placeY L y j'' u = j u' := range_le L hca hcaY' hlp hlpY'
    choose f hf using hex
    have hinj := hpl.1
    have hadd : ∀ u v, f (u + v) = f u + f v := fun u v => hinj (by simp only [map_add, hf])
    have hsmul : ∀ (c : D.O) u, f (c • u) = c • f u := fun c u => hinj (by
      rw [hf, hpl.2.1, hf, placeY_apply, placeY_apply, hpl''.2.1, (hA p D G L B.β y).2.1])
    let fl : D''.La →ₗ[D.O] D'.La := { toFun := f, map_add' := hadd, map_smul' := hsmul }
    have hYinj : Function.Injective (placeY L y j'') := by
      intro u v huv
      rw [placeY_apply, placeY_apply] at huv
      have e := congrArg (actY L y⁻¹) huv
      rw [inv_actY, inv_actY] at e
      exact hpl''.1 e
    have hbij : Function.Bijective fl := by
      refine ⟨fun u v huv => hYinj ?_, fun u' => ?_⟩
      · rw [← hf, ← hf]
        exact congrArg j huv
      · obtain ⟨u, hu⟩ := hex' u'
        exact ⟨u, hinj ((hf u).trans hu)⟩
    let w := LinearEquiv.ofBijective fl hbij
    have hjw : ∀ u, j (w u) = actY L y (j'' u) := fun u => hf u
    obtain ⟨s, hs, hsf⟩ := hpl.2.2.2
    obtain ⟨s'', hs'', hsf''⟩ := hpl''.2.2.2
    have hy2 : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    have hsc : ∀ u u' : D''.La, (((D'.EF (w u)) (w u') : ℤ) : ℚ) =
        s * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) / s'' * (((D''.EF u) u' : ℤ) : ℚ) := by
      intro u u'
      rw [hsf, hjw, hjw, (hA p D G L B.β y).1, hsf'']
      field_simp
    have hr := hS p D N₁ N₂ D' t₁ D'' t₂ hc₁ hc₂ w.toAddEquiv _ (by positivity) hsc
    have hiso : IsIsom D'' D' w := by
      intro u u'
      have e := hsc u u'
      rw [hr, _root_.one_mul] at e
      exact_mod_cast e
    refine ⟨w, ⟨hiso, fun a0 => ?_⟩, hjw⟩
    obtain ⟨w1, hw1, e1⟩ := hca.2 a0
    obtain ⟨w2, hw2, e2⟩ := hcaY'.2 a0
    have hd : rd L (trivX B) a.1 (j (w (t'' a0) - t a0)) = N • (w2 - w1) := by
      rw [map_sub, rd_sub, hjw, ← placeY_apply, e2, e1, smul_sub]
      abel
    obtain ⟨e, he⟩ := mark_div L hN hNp hinj hca.1 _ (sub_mem hw2 hw1) hd
    exact ⟨e, eq_add_of_sub_eq' he⟩
  · rintro ⟨w, ⟨hiso, hmark⟩, hjw⟩
    have hjY : ∀ u, placeY L y j'' u = j (w u) := fun u => (hjw u).symm
    have hcaY' : IsCoordA L (trivX B) N D'' t'' (placeY L y j'') a.1 := by
      refine ⟨fun w0 => ?_, fun a0 => ?_⟩
      · rw [← hca.1 w0]
        constructor
        · rintro ⟨r, u, hu⟩
          exact ⟨r, w u, by rw [hu, hjY]⟩
        · rintro ⟨r, u, hu⟩
          exact ⟨r, w.symm u, by rw [hu, hjY, LinearEquiv.apply_symm_apply]⟩
      · obtain ⟨e, he⟩ := hmark a0
        obtain ⟨w1, hw1, e1⟩ := hca.2 a0
        have he' : rd L (trivX B) a.1 (j e) ∈ LaHat D := (hca.1 (j e)).1 ⟨0, e, by simp⟩
        refine ⟨w1 + rd L (trivX B) a.1 (j e), add_mem hw1 he', ?_⟩
        rw [hjY, he, map_add, map_nsmul, rd_add, rd_nsmul, e1, smul_add, add_assoc]
    have hkn := (hK p D G L (trivX B) N hN hNp D'' t'' (placeY L y j'') _ _ hcaY).1 hcaY'
    have hlpY' : IsLocP D'' (placeY L y j'') (PD.lat a.2) := by
      intro w0
      rw [← hlp w0]
      constructor
      · rintro ⟨m, u, hm, hu⟩
        exact ⟨m, w u, hm, by rw [hu, hjY]⟩
      · rintro ⟨m, u, hm, hu⟩
        exact ⟨m, w.symm u, hm, by rw [hu, hjY, LinearEquiv.apply_symm_apply]⟩
    have hlat : PD.lat a.2 = PD.lat (GlobalTheory.LKCx.toP1 G B.β y * a''.2) := by
      ext w0
      rw [← hlpY' w0, ← hlpY w0]
    have hkh := (PD.inj _ _).1 hlat
    exact ⟨by rw [_root_.mul_assoc]; exact hkn, by rw [_root_.mul_assoc]; exact hkh⟩
