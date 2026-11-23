import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.FlDefs

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Fl

section Blocks

variable {R S : Type} [CommRing R] [CommRing S] {c N : ℕ} {n : Fin c → ℕ}

theorem one_apply_blk (e : (Σ a, Fin (n a)) ≃ Fin N) (a : Fin c) (i j : Fin (n a)) :
    (1 : Matrix (Fin N) (Fin N) R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (Fin (n a)) (Fin (n a)) R) i j := by
  simp [Matrix.one_apply]

theorem one_apply_blk_ne (e : (Σ a, Fin (n a)) ≃ Fin N) {a b : Fin c} (h : a ≠ b) (i : Fin (n a)) (j : Fin (n b)) :
    (1 : Matrix (Fin N) (Fin N) R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  rw [Matrix.one_apply_ne]
  intro h'
  exact h (congrArg Sigma.fst (e.injective h'))

theorem cornerGL_apply {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g : Matrix (Fin a) (Fin a) S) i j =
      (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g : Matrix (Fin a) (Fin a) R) i j) :=
  rfl

theorem cornerGL_leviEmb (e : (Σ a, Fin (n a)) ≃ Fin N) (s : R →ₙ+* S) (m : ∀ a, GL (Fin (n a)) R) :
    cornerGL N s (leviEmb R e m) = leviEmb S e fun a => cornerGL (n a) s (m a) := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  rw [cornerGL_apply]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same, cornerGL_apply, one_apply_blk, one_apply_blk]
  · rw [leviEmb_apply_ne R e m hab, leviEmb_apply_ne S e _ hab, one_apply_blk_ne e hab,
      one_apply_blk_ne e hab, map_zero]
    simp

theorem cornerGL_mem_unipRad (e : (Σ a, Fin (n a)) ≃ Fin N) (s : R →ₙ+* S) {u : GL (Fin N) R}
    (hu : u ∈ unipRad R e) : cornerGL N s u ∈ unipRad S e := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hu
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := fun h' => by subst h'; exact lt_irrefl _ hij
    rw [cornerGL_apply, h1 hij, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne, map_zero]
    simp
  · rw [cornerGL_apply, h2 a i j, one_apply_blk, one_apply_blk]
    simp

end Blocks

variable {E : Type} [Field E] [NumberField E]

theorem glAf_ext {N : ℕ} {x y : GL (Fin N) (Af E)}
    (H : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) :
    x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_
  have := congrArg (fun z : GL (Fin N) (v.adicCompletion E) => z.val i j) (H v)
  simp only [GeneralLinearGroup.map_apply] at this
  exact this

theorem locGL_commute {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) (x : GL (Fin N) (Af E)) (g : GL (Fin N) (w.adicCompletion E))
    (hx : GeneralLinearGroup.map (pLoc E w) x = 1) : locGL E N w g * x = x * locGL E N w g := by
  refine glAf_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [hx, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

variable {N : ℕ} {w : HeightOneSpectrum (𝓞 E)}

theorem wPart_apply (g : GA E N) :
    wPart N w g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  ext i j
  rfl

theorem wPart_iota (x : GL (Fin N) (w.adicCompletion E)) : wPart N w (iota N w x) = x := by
  rw [wPart_apply, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL]

theorem wPart_awayPart (g : GA E N) : wPart N w (awayPart N w g) = 1 := by
  rw [awayPart, map_mul, map_inv, wPart_iota, mul_inv_cancel]

theorem awayPart_mul_iota_wPart (g : GA E N) : awayPart N w g * iota N w (wPart N w g) = g := by
  rw [awayPart, inv_mul_cancel_right]

theorem commute_iota [IsTotallyComplex E] {y : GA E N} (hy : wPart N w y = 1) (x : GL (Fin N) (w.adicCompletion E)) :
    y * iota N w x = iota N w x * y := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, MonoidHom.comp_apply, pInf_finGL, mul_one, one_mul]
  · simp only [map_mul, MonoidHom.comp_apply, pFin_finGL]
    refine (locGL_commute w _ x ?_).symm
    rw [← wPart_apply]
    exact hy

variable {c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N)

theorem iota_leviEmb (x : ∀ i, GL (Fin (n i)) (w.adicCompletion E)) :
    iota N w (leviEmb (w.adicCompletion E) (stdBlocks n h) x) =
      leviEmb (Ad E) (stdBlocks n h) fun i => iota (n i) w (x i) := by
  change cornerGL N (sFin E) (cornerGL N (sLoc E w) _) = _
  rw [cornerGL_leviEmb, cornerGL_leviEmb]
  rfl

theorem iota_mem_unipRad {u : GL (Fin N) (w.adicCompletion E)} (hu : u ∈ unipRad (w.adicCompletion E) (stdBlocks n h)) :
    iota N w u ∈ unipRad (Ad E) (stdBlocks n h) := by
  change cornerGL N (sFin E) (cornerGL N (sLoc E w) u) ∈ _
  exact cornerGL_mem_unipRad _ _ (cornerGL_mem_unipRad _ _ hu)

end PositivityTheory.Rg.Rs.C3.Fl

end
