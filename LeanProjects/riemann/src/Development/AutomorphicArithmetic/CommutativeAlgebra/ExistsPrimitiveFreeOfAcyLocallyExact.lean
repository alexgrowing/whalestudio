import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSuppOfSectionsV
import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyAndLiftOfLocallySurjectiveExact

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem sec_comp {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

private theorem sec_zero {F G : Shv ℤ} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

private theorem UpperTheory.sec_map_res_comm {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) =
    (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem UpperTheory.injective_sec_map_of_mono {F G : Shv ℤ} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

private theorem UpperTheory.acy_of_isZero (Q : Scheme.{0} → Prop) (G : Shv ℤ) (hG : IsZero G) :
    Acy Q G := by
  intro P hP n _
  have hid : (𝟙 G : G ⟶ G) = 0 := hG.eq_of_src _ _
  have hsub : ∀ {U : Scheme.{0}} (x : Sec G U), x = 0 := fun {U} x => by
    calc x = Sec.map (𝟙 G) x := rfl
      _ = 0 := by rw [hid, sec_zero]
  exact UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q G (fun U _ => ⟨fun x y => by rw [hsub x, hsub y]⟩) P hP n

theorem UpperTheory.exists_primitive_free_of_acy_locally_exact :
    ∀ (C : Cx ℤ) (a : ℤ) [C.IsStrictlyGE a] (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → (∀ s, Acy Q (C.X s)) → (∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) c = Sec.res g b) → ∀ P : PSh, Supp Q P → ∀ (j : ℤ) (f : (free ℤ).obj P ⟶ C.X j), f ≫ C.d j (j + 1) = 0 → ∃ g : (free ℤ).obj P ⟶ C.X (j - 1), g ≫ C.d (j - 1) j = f := by
  intro C a _ Q hQ hacy hexact P hP j f hf
  have step : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) →
      Acy Q (kernel (C.d (i + 1) (i + 1 + 1))) ∧ ∀ P : PSh, Supp Q P →
        ∀ f : (free ℤ).obj P ⟶ kernel (C.d (i + 1) (i + 1 + 1)),
          ∃ h, h ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
            (C.d_comp_d _ _ _) = f := by
    intro i hi
    have w : kernel.ι (C.d i (i + 1)) ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
        (C.d_comp_d _ _ _) = 0 := by
      rw [← cancel_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))), Category.assoc, kernel.lift_ι,
        kernel.condition, zero_comp]
    have hex : (ShortComplex.mk (kernel.ι (C.d i (i + 1)))
        (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _)) w).Exact := by
      apply ShortComplex.exact_of_f_is_kernel
      refine KernelFork.IsLimit.ofι _ _
        (fun g' hg' => kernel.lift (C.d i (i + 1)) g' (by
          rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
            ← Category.assoc, hg', zero_comp]))
        (fun g' hg' => kernel.lift_ι _ _ _)
        (fun g' hg' m hm => by
          rw [← cancel_mono (kernel.ι (C.d i (i + 1))), kernel.lift_ι]
          exact hm)
    have hloc : ∀ U : Scheme.{0}, Q U → ∀ b : Sec (kernel (C.d (i + 1) (i + 1 + 1))) U,
        Loc U fun V g => ∃ c, Sec.map (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
          (C.d_comp_d _ _ _)) c = Sec.res g b := by
      intro U hU b
      have hb : Sec.map (C.d (i + 1) (i + 1 + 1))
          (Sec.map (kernel.ι (C.d (i + 1) (i + 1 + 1))) b) = 0 := by
        rw [← sec_comp, kernel.condition, sec_zero]
      have h1 := hexact U hU (i + 1) _ hb
      rw [show i + 1 - 1 = i by omega] at h1
      obtain ⟨S, hS, hSp⟩ := h1
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨c, hc⟩ := hSp V g hg
      refine ⟨c, UpperTheory.injective_sec_map_of_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))) V ?_⟩
      show Sec.map _ (Sec.map _ c) = Sec.map _ (Sec.res g b)
      rw [← sec_comp, kernel.lift_ι, hc, UpperTheory.sec_map_res_comm]
    exact UpperTheory.acy_and_lift_of_locally_surjective_exact Q @hQ _ _ _ _ _ w inferInstance hex hloc hi (hacy i)
  have hAcy : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) := by
    intro i
    rcases lt_or_ge i a with hi | hi
    · exact UpperTheory.acy_of_isZero Q _ (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a i hi))
    · have hi' : a - 1 ≤ i := by omega
      induction i, hi' using Int.le_induction with
      | base =>
        exact UpperTheory.acy_of_isZero Q _
          (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a (a - 1) (by omega)))
      | succ n hn ih =>
        rcases lt_or_ge n a with hn' | hn'
        · exact (step n (UpperTheory.acy_of_isZero Q _
            (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a n hn')))).1
        · exact (step n (ih hn')).1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [show i + 1 - 1 = i by omega]
  obtain ⟨h, hh⟩ := (step i (hAcy i)).2 P hP (kernel.lift _ f hf)
  refine ⟨h, ?_⟩
  rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
    ← Category.assoc, hh, kernel.lift_ι]
