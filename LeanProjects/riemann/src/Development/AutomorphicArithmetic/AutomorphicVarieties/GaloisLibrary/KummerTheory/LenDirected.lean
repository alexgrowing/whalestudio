import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.lenDirected :
    ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (W : Submodule R X) (P : ℕ → Submodule R X) (Bd : ℕ∞), Monotone P → W ≤ ⨆ n, P n →
    (∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (P n) ≤ Bd) → Module.length R W ≤ Bd := by
  intro R X _ _ _ W P Bd hP hW hBd
  classical
  rw [← WithBot.coe_le_coe, Module.coe_length, Order.krullDim, iSup_le_iff]
  intro p
  have hstep : ∀ i : Fin p.length, ∃ x : W, x ∈ p i.succ ∧ x ∉ p i.castSucc := by
    intro i
    exact SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hstep
  have hdir : Directed (· ≤ ·) P := hP.directed_le
  have hmem : ∀ i : Fin p.length, ∃ n, (x i : X) ∈ P n := by
    intro i
    exact (Submodule.mem_iSup_of_directed P hdir).mp (hW (x i).2)
  choose m hm using hmem
  obtain ⟨n, hn, hlen⟩ := hBd (Finset.univ.sup m)
  have hxn : ∀ i, (x i : X) ∈ P n := by
    intro i
    exact hP ((Finset.le_sup (Finset.mem_univ i)).trans hn) (hm i)
  let f : Submodule R W → Submodule R (P n) := fun S => (S.map W.subtype).comap (P n).subtype
  have hfmono : Monotone f := by
    intro S T hST
    exact Submodule.comap_mono (Submodule.map_mono hST)
  let q : LTSeries (Submodule R (P n)) :=
    { length := p.length
      toFun := fun i => f (p i)
      step := by
        intro i
        refine lt_of_le_of_ne (hfmono (p.step i).le) ?_
        intro heq
        have h1 : (⟨(x i : X), hxn i⟩ : P n) ∈ f (p i.succ) := by
          simp only [f, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map]
          exact ⟨x i, hx1 i, rfl⟩
        rw [← heq] at h1
        simp only [f, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map] at h1
        obtain ⟨y, hy, hyx⟩ := h1
        have : y = x i := Subtype.ext hyx
        exact hx2 i (this ▸ hy) }
  have hq := Order.LTSeries.length_le_krullDim q
  rw [← Module.coe_length] at hq
  exact hq.trans (WithBot.coe_le_coe.mpr hlen)
