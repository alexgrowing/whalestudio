import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLUBRangeOfMatch
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.DeKeyTrue GlobalTheory.Toroidal
open CategoryTheory

open AlgebraicGeometry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.LiftOrth

theorem exists_lift_hodge : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag) (σ : D.what₂.LL →+* ℂ) (k : (s.U (Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ))).Comp) (xx : ((s.U (Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ))).X k).dom), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((s.U (Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ))).X k) xx.1 → ∃ (ψ : ℂ →+* ℂ) (q : Σ k : s.Comp, (geoTrue D.what₂.LL).pts (Φ.C k).Y σ) (g : (Φ.C q.1).FrameAt q.2), (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) ∧ Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ) = ψ.comp (GlobalTheory.ShFam.embOf κ.e σ) ∧ IsHodgeFrame s.U ((Φ.C q.1).down q.2) g ∧ (Φ.C q.1).Carries q.2.1 g ∧ ((Φ.C q.1).down q.2).1 = spMap ψ ≫ (cxPt s.T.Z ((s.U (Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ))).un k xx)).1 ∧ (cxFrame s.T.Z ((s.U (Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ))).un k xx)).IsMap ψ g := by
  intro D A N j S κ s Φ σ k xx hx
  obtain ⟨ψ, hψ, hψσ, hψψ⟩ : ∃ ψ : ℂ →+* ℂ, (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) ∧
      Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ) = ψ.comp (GlobalTheory.ShFam.embOf κ.e σ) ∧
      ψ.comp ψ = RingHom.id ℂ := by
    by_cases h : Formalism.L2.PjFree.GoodEmb κ.c (GlobalTheory.ShFam.embOf κ.e σ)
    · exact ⟨RingHom.id ℂ, .inl rfl, by rw [Formalism.L2.PjFree.goodOf, if_pos h]; rfl, rfl⟩
    · exact ⟨starRingEnd ℂ, .inr rfl, by rw [Formalism.L2.PjFree.goodOf, if_neg h], RingHom.ext Complex.conj_conj⟩
  have hcc : spMap ψ ≫ spMap ψ = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext hψψ)
  set y := (s.U (Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ))).un k xx with hy
  obtain ⟨X, hX⟩ : ∃ X : Sp ℂ ⟶ gen s.T.Z, X = spMap ψ ≫ (cxPt s.T.Z y).1 := ⟨_, rfl⟩
  have hXs : X ≫ genStr s.T.Z = spMap (GlobalTheory.ShFam.embOf κ.e σ) := by
    rw [hX, Category.assoc, (cxPt s.T.Z y).2, hψσ]
    rw [← OpenReg.spMap_comp, ← Category.assoc, hcc, Category.id_comp]
  have hφ : GlobalTheory.ShFam.embOf κ.e σ = ψ.comp (Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ)) := by
    rw [hψσ, ← RingHom.comp_assoc, hψψ, RingHom.id_comp]
  obtain ⟨g₀, hg₀⟩ := (cxFrame s.T.Z y).exists_isMap ψ (φ' := GlobalTheory.ShFam.embOf κ.e σ) (x' := X ≫ genι s.T.Z) hφ
    (by rw [hX, Category.assoc])
  obtain ⟨⟨i, p⟩, ⟨hp, hc⟩, -⟩ := Φ.lifts ℂ (GlobalTheory.ShFam.embOf κ.e σ) X hXs g₀
  dsimp only at hp hc
  subst hp
  have hps : p ≫ (Φ.C i).Y.str = spMap σ := by
    rw [← (Φ.C i).π_str, ← Category.assoc, ← Category.assoc, hXs]
    rw [OpenReg.spMap_comp]
    exact congrArg spMap (RingHom.ext fun a => by simp)
  refine ⟨ψ, ⟨i, ⟨p, hps⟩⟩, g₀, hψ, hψσ, ⟨ψ, _, k, xx, hψ, hψσ, Formalism.L2.PjFree.goodEmb_goodOf _ _, hx, ?_, ?_⟩,
    hc, hX, hg₀⟩
  · show (cxPt s.T.Z y).1 = spMap ψ ≫ p ≫ (Φ.C i).π
    rw [hX, ← Category.assoc, hcc, Category.id_comp]
  · intro τ b
    rw [hg₀ τ b, GlobalTheory.GradedPieces.dual_comp, hψψ, spMap_dualMap_id, Category.id_comp]

end GlobalTheory.ShFam.LiftOrth
