import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem continuous_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] {a : ℕ} (f : A →+* B) (hf : Continuous f) (ρ : Γ →* GL (Fin a) A)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A)) :
    Continuous fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) := by
  have : (fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B)) =
      fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f := by
    funext g; rfl
  rw [this]
  exact hρ.matrix_map hf

end GlobalTheory.HeightCounting.PhtExt

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

noncomputable def ext (Wd₀ : WDSide D T) : WDSide D T :=
  { Wd₀ with
    IsdRW := fun l _ ι a r w =>
      (Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ Wd₀.IsdRW l ι r w
    wdOf_unrL := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_unrL l ι r w hw hc hd.2
    wdOf_mono0L := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_mono0L l ι r w hw hc hd.2
    loc := by
      intro l _ ι w hw O _ _ _ Bw hB φ hφ
      obtain ⟨h1, h2⟩ := Wd₀.loc l ι w hw O Bw hB φ hφ
      have hφc : Continuous φ := by
        have e : (φ : O → Qbar l) = fun x => ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) := funext hφ
        rw [e]
        unfold LocBridge.toLL
        exact continuous_subtype_val.comp (continuous_subtype_val.comp Bw.eO_cont)
      refine ⟨fun m ρ hρ => ?_, fun LL' hLL' m ρ hρ => ?_⟩
      · obtain ⟨c1, c2, c3, c4⟩ := h1 m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep φ hφc ρ hρ)).trans c2, c3, c4⟩
      · have hf : Continuous (algebraMap ↥LL'.1 (Qbar l)) := continuous_subtype_val
        obtain ⟨c1, c2, c3, c4⟩ := h2 LL' hLL' m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep _ hf ρ hρ)).trans c2, c3, c4⟩ }

theorem exists_phtOn_all : PhtCmp → ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), WDSide D T →
    ∃ Wd : WDSide D T, PhtOn Wd fr fun _ _ _ _ => True := by
  intro hP D fr T Wd₀
  exact ⟨ext Wd₀, ⟨fun l _ ι a r τ w _ hw hd => (hP D fr T Wd₀).card l ι a r τ w hd.1 hw hd.2⟩⟩

end GlobalTheory.HeightCounting.PhtExt
