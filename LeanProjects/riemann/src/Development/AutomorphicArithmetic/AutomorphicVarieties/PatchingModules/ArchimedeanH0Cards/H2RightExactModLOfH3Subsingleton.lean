import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

section

variable {k G M : Type} [CommRing k] [Group G] [AddCommGroup M] [Module k M]

end

private theorem dn_two_apply' {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (rho : Representation R G M) (F : (Fin 2 → G) → M) (g : Fin 3 → G) :
    dn rho 2 F g = rho (g 0) (F ![g 1, g 2]) - F ![g 0 * g 1, g 2] + F ![g 0, g 1 * g 2] - F ![g 0, g 1] := by
  have e0 : (fun i : Fin 2 => g i.succ) = ![g 1, g 2] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x y : G => x * y) g = ![g 0 * g 1, g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e2 : Fin.contractNth 1 (fun x y : G => x * y) g = ![g 0, g 1 * g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e3 : Fin.contractNth 2 (fun x y : G => x * y) g = ![g 0, g 1] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.sum_univ_zero, e0, e1]
  norm_num
  rw [e2, e3]
  abel

private theorem dn_three_apply {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (rho : Representation R G M) (F : (Fin 3 → G) → M) (g : Fin 4 → G) :
    dn rho 3 F g = rho (g 0) (F ![g 1, g 2, g 3]) - F ![g 0 * g 1, g 2, g 3] + F ![g 0, g 1 * g 2, g 3]
      - F ![g 0, g 1, g 2 * g 3] + F ![g 0, g 1, g 2] := by
  have e0 : (fun i : Fin 3 => g i.succ) = ![g 1, g 2, g 3] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x y : G => x * y) g = ![g 0 * g 1, g 2, g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e2 : Fin.contractNth 1 (fun x y : G => x * y) g = ![g 0, g 1 * g 2, g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e3 : Fin.contractNth 2 (fun x y : G => x * y) g = ![g 0, g 1, g 2 * g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e4 : Fin.contractNth 3 (fun x y : G => x * y) g = ![g 0, g 1, g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.sum_univ_zero, e0, e1]
  norm_num
  rw [e2, e3, show (Fin.succ 2 : Fin 4) = 3 from rfl, e4]
  abel

theorem UpperTheory.V.Pa.B2.H2_right_exact_mod_l_of_H3_subsingleton :
    ∀ (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ (A : Type) [CommRing A] (M : FRep A G), (∀ m : M.X, l • m = 0) → Subsingleton (Hn M.ρ 3)) → SecondCohomologyRightExactModL l G := by
  intro l G _ _ _ h A _ M M' hl u hu hs
  intro x
  obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ x
  set s := Function.surjInv hs with hs_def
  have us : ∀ y, u (s y) = y := Function.surjInv_eq hs
  let c : G × G → M.X := fun p => s (c'.1 p)
  have hc : Continuous c := (continuous_of_discreteTopology (f := s)).comp c'.2.1
  let N : Submodule A M.X := LinearMap.ker u
  have hN : ∀ g : G, ∀ m ∈ N, M.ρ g m ∈ N := by
    intro g m hm
    simp only [N, LinearMap.mem_ker] at hm ⊢
    rw [hu, hm, map_zero]
  let ρK : Representation A G N :=
    { toFun := fun g => (M.ρ g).restrict (hN g)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro g g'
        ext m
        simp }
  have hcont : ContAction ρK :=
    continuous_induced_rng.2 (M.cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let K : FRep A G := FRep.mk N ρK hcont
  have hKl : ∀ m : K.X, l • m = 0 := by
    intro m
    exact Subtype.ext (hl m.1)
  have hsub := h A K hKl
  let C : (Fin 2 → G) → M.X := fun x => c (x 0, x 1)
  have hfN : ∀ g : Fin 3 → G, dn M.ρ 2 C g ∈ N := by
    intro g
    simp only [N, LinearMap.mem_ker]
    rw [dn_two_apply']
    simp only [C, c, map_sub, map_add, hu, us]
    simpa using c'.2.2 (g 0) (g 1) (g 2)
  let f : (Fin 3 → G) → N := fun g => ⟨dn M.ρ 2 C g, hfN g⟩
  have key : ∀ t : Fin 3 → G, ((f t : N) : M.X) =
      M.ρ (t 0) (c (t 1, t 2)) - c (t 0 * t 1, t 2) + c (t 0, t 1 * t 2) - c (t 0, t 1) := by
    intro t
    simp [f, dn_two_apply', C]
  have hρK : ∀ (a : G) (m : N), ((ρK a m : N) : M.X) = M.ρ a m := fun a m => rfl
  have hmul : ∀ (a b : G) (m : M.X), M.ρ a (M.ρ b m) = M.ρ (a * b) m := by
    intro a b m
    simp [map_mul]
  have fcont : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f) = fun t : Fin 3 → G =>
        M.ρ (t 0) (c (t 1, t 2)) - c (t 0 * t 1, t 2) + c (t 0, t 1 * t 2) - c (t 0, t 1) := funext key
    rw [e]
    have c0 := continuous_apply (A := fun _ : Fin 3 => G) 0
    have c1 := continuous_apply (A := fun _ : Fin 3 => G) 1
    have c2 := continuous_apply (A := fun _ : Fin 3 => G) 2
    exact (((M.cont.comp (c0.prodMk (hc.comp (c1.prodMk c2)))).sub
      (hc.comp ((c0.mul c1).prodMk c2))).add (hc.comp (c0.prodMk (c1.mul c2)))).sub
      (hc.comp (c0.prodMk c1))
  have fcyc : dn ρK 3 f = 0 := by
    funext g
    apply Subtype.ext
    rw [dn_three_apply]
    simp only [Submodule.coe_add, Submodule.coe_sub, hρK, key, Pi.zero_apply, ZeroMemClass.coe_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_sub, map_add, hmul]
    simp only [mul_assoc]
    abel
  have fmem : f ∈ Zn K.ρ 3 := by
    refine Submodule.mem_inf.2 ⟨fcont, ?_⟩
    exact LinearMap.mem_ker.2 fcyc
  have h0 : (Submodule.Quotient.mk ⟨f, fmem⟩ : Hn K.ρ 3) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
  change f ∈ Submodule.map (dn ρK 2) (Cn ρK 2) at h0
  obtain ⟨b, hb, hbf⟩ := h0
  have hbc : Continuous b := hb
  have hv : Continuous fun p : G × G => ![p.1, p.2] := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  let c2 : G × G → M.X := fun p => c p - (b ![p.1, p.2] : M.X)
  have hc2 : c2 ∈ Z2 M.ρ := by
    refine ⟨hc.sub (continuous_subtype_val.comp (hbc.comp hv)), ?_⟩
    intro g g' g''
    have e := congrArg Subtype.val (congrFun hbf ![g, g', g''])
    rw [dn_two_apply'] at e
    simp only [Submodule.coe_add, Submodule.coe_sub, hρK, key, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e
    simp only [c2, map_sub]
    calc _ = (M.ρ g (c (g', g'')) - c (g * g', g'') + c (g, g' * g'') - c (g, g'))
          - (M.ρ g (b ![g', g''] : M.X) - (b ![g * g', g''] : M.X) + (b ![g, g' * g''] : M.X)
            - (b ![g, g'] : M.X)) := by abel
      _ = 0 := by rw [e, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨c2, hc2⟩, ?_⟩
  simp only [mapH2, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  funext p
  show u (c2 p) = c'.1 p
  simp only [c2, c, map_sub, us, LinearMap.mem_ker.1 (b _).2, sub_zero]
