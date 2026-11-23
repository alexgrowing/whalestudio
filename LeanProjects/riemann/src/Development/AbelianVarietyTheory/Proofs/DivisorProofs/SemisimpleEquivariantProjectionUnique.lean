import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso

theorem GlobalTheory.LocFinIso.hermitian_matrix_of_commuting_idempotent : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (h1 : (1 : G) ∈ K) (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D), IsSemisimpleModule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule → ∀ (P : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)] (repD ρ D K h1 hmul hst).asModule), (∀ v, P (P v) = P v) → (∀ g : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)] (repD ρ D K h1 hmul hst).asModule, ∀ v, P (g v) = g (P v)) → ∀ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ) (hbD : ∀ i, b i ∈ D), LinearIndependent ℂ b → (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) → (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) → ∃ Pm : Matrix (Fin m) (Fin m) ℂ, (∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ∑ i, Pm i j • b i) ∧ star Pm = Pm := by
  intro G _ K V _ _ ρ D h1 hmul hst hss P hPP hPc m b A hbD hli hAct hU
  haveI := hss
  set e := (repD ρ D K h1 hmul hst).asModuleEquiv with he
  set Sb : Submodule ℂ V := Submodule.span ℂ (Set.range b) with hSb
  have hSbD : Sb ≤ D := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbD i)
  have hstab : ∀ k ∈ K, ∀ x ∈ Sb, ρ k x ∈ Sb := by
    intro k hk x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [hAct k hk j]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  let W : Submodule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule :=
    { carrier := {u | ((e u : D) : V) ∈ Sb}
      add_mem' := by
        intro u v hu hv
        simp only [Set.mem_setOf_eq, map_add, Submodule.coe_add] at *
        exact Submodule.add_mem _ hu hv
      zero_mem' := by simp
      smul_mem' := by
        intro a u hu
        simp only [Set.mem_setOf_eq] at *
        rw [he, smul_val]
        exact Submodule.sum_mem _ (fun κ _ => Submodule.smul_mem _ _ (hstab κ κ.2 _ hu)) }
  have hWmem : ∀ u, u ∈ W ↔ ((e u : D) : V) ∈ Sb := fun u => Iff.rfl
  obtain ⟨C, hC⟩ := exists_isCompl W
  let π := W.subtype ∘ₗ W.projectionOnto C hC
  have hπW : ∀ u ∈ W, π u = u := fun u hu => by
    show ((W.projectionOnto C hC ((⟨u, hu⟩ : W) : _)) : _) = u
    rw [Submodule.projectionOnto_apply_left]
  have hπmem : ∀ u, π u ∈ W := fun u => (W.projectionOnto C hC u).2
  have hPW : ∀ u ∈ W, P u ∈ W := fun u hu => by
    rw [← hπW u hu, hPc π]; exact hπmem _

  let Bs := Module.Basis.span hli
  have hBs : ∀ j, ((Bs j : Sb) : V) = b j := fun j => by simp [Bs, Module.Basis.span_apply]
  let incl : Sb →ₗ[ℂ] D := Submodule.inclusion hSbD
  have hinclBs : ∀ j, incl (Bs j) = ⟨b j, hbD j⟩ := fun j => Subtype.ext (hBs j)
  let ρS : ∀ k ∈ K, Sb →ₗ[ℂ] Sb := fun k hk => (ρ k).restrict (hstab k hk)
  have hρS : ∀ k (hk : k ∈ K), ρS k hk = Matrix.toLin Bs Bs (A k) := by
    intro k hk
    refine Bs.ext (fun j => ?_)
    rw [Matrix.toLin_self]
    apply Subtype.ext
    simp [ρS, LinearMap.restrict_apply, hBs, hAct k hk j]
  have hTPmem : ∀ x : Sb, ((e (P (e.symm (incl x))) : D) : V) ∈ Sb := fun x => by
    have : e.symm (incl x) ∈ W := by rw [hWmem]; simp [incl]
    exact hPW _ this
  let TP : Sb →ₗ[ℂ] Sb :=
    LinearMap.codRestrict Sb (D.subtype ∘ₗ (toEndD ρ D K h1 hmul hst P) ∘ₗ incl) hTPmem
  have hTP : ∀ x, ((TP x : Sb) : V) = ((e (P (e.symm (incl x))) : D) : V) := fun x => rfl
  let Pm := LinearMap.toMatrix Bs Bs TP
  have hform : ∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ∑ i, Pm i j • b i := by
    intro j
    have h1' : ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ((TP (Bs j) : Sb) : V) := by
      rw [hTP, hinclBs]; rfl
    rw [h1']
    conv_lhs => rw [← Matrix.toLin_toMatrix Bs Bs TP]
    rw [Matrix.toLin_self]
    simp [hBs, Pm]

  have hinclTP : ∀ x, incl (TP x) = e (P (e.symm (incl x))) := fun x => Subtype.ext (hTP x)
  have hidem : Pm * Pm = Pm := by
    have h : TP ∘ₗ TP = TP := by
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ((TP (TP x) : Sb) : V) = ((TP x : Sb) : V)
      rw [hTP, hinclTP, LinearEquiv.symm_apply_apply, hPP]
      exact (hTP x).symm
    calc Pm * Pm = LinearMap.toMatrix Bs Bs (TP ∘ₗ TP) := (LinearMap.toMatrix_comp Bs Bs Bs TP TP).symm
      _ = Pm := by rw [h]
  have hmatA : ∀ k (hk : k ∈ K), LinearMap.toMatrix Bs Bs (ρS k hk) = A k := fun k hk => by
    rw [hρS k hk, LinearMap.toMatrix_toLin]
  have hcommA : ∀ k ∈ K, Pm * A k = A k * Pm := by
    intro k hk
    have h : TP ∘ₗ ρS k hk = ρS k hk ∘ₗ TP := by
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ((TP (ρS k hk x) : Sb) : V) = ρ k ((TP x : Sb) : V)
      rw [hTP, hTP]
      have h2 : incl (ρS k hk x) = (repD ρ D K h1 hmul hst ⟨k, hk⟩) (incl x) := Subtype.ext rfl
      rw [h2, he, Representation.asModuleEquiv_symm_map_rho, P.map_smul,
        Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
      rfl
    rw [← hmatA k hk, ← LinearMap.toMatrix_comp Bs Bs Bs, h, LinearMap.toMatrix_comp Bs Bs Bs]

  have hcommQ : ∀ Q : Matrix (Fin m) (Fin m) ℂ, (∀ k ∈ K, Q * A k = A k * Q) → Pm * Q = Q * Pm := by
    intro Q hQ
    let LQ := Matrix.toLin Bs Bs Q
    have hLQ : ∀ k (hk : k ∈ K) x, LQ (ρS k hk x) = ρS k hk (LQ x) := by
      intro k hk x
      rw [hρS k hk]
      show (LQ ∘ₗ Matrix.toLin Bs Bs (A k)) x = (Matrix.toLin Bs Bs (A k) ∘ₗ LQ) x
      rw [← Matrix.toLin_mul Bs Bs Bs, ← Matrix.toLin_mul Bs Bs Bs, hQ k hk]
    have hsmulV : ∀ (a : MonoidAlgebra ℂ (subK K h1 hmul)) (y : (repD ρ D K h1 hmul hst).asModule),
        ((e (a • y) : D) : V) = ∑ κ ∈ a.coeff.support, a.coeff κ • ρ κ ((e y : D) : V) :=
      fun a y => smul_val ρ D K h1 hmul hst a y
    let g : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)]
        (repD ρ D K h1 hmul hst).asModule :=
      { toFun := fun u => e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩))
        map_add' := by
          intro u v
          have h : (⟨((e (π (u + v)) : D) : V), hπmem (u + v)⟩ : Sb) =
              ⟨((e (π u) : D) : V), hπmem u⟩ + ⟨((e (π v) : D) : V), hπmem v⟩ :=
            Subtype.ext (by simp)
          show e.symm (incl (LQ ⟨((e (π (u + v)) : D) : V), hπmem (u + v)⟩)) =
            e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩)) + e.symm (incl (LQ ⟨((e (π v) : D) : V), hπmem v⟩))
          rw [h, map_add, map_add, map_add]
        map_smul' := by
          intro a u
          apply e.injective
          apply Subtype.ext
          show ((e (e.symm (incl (LQ ⟨((e (π (a • u)) : D) : V), hπmem (a • u)⟩)))) : V) =
            ((e (a • e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩)))) : V)
          rw [hsmulV, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          have key : (⟨((e (π (a • u)) : D) : V), hπmem (a • u)⟩ : Sb) =
              ∑ κ ∈ a.coeff.support, a.coeff κ • ρS κ κ.2 ⟨((e (π u) : D) : V), hπmem u⟩ := by
            apply Subtype.ext
            rw [Submodule.coe_sum]
            simp only [Submodule.coe_smul, ρS, LinearMap.restrict_apply]
            show ((e (π (a • u)) : D) : V) = _
            rw [π.map_smul a u, hsmulV]
          rw [key, map_sum]
          simp only [map_smul, hLQ]
          rw [map_sum, Submodule.coe_sum]
          simp only [map_smul, Submodule.coe_smul]
          refine Finset.sum_congr rfl (fun κ _ => ?_)
          rw [hLQ κ κ.2]
          rfl }
    have hg : ∀ w (hw : w ∈ W), g w = e.symm (incl (LQ ⟨((e w : D) : V), hw⟩)) := by
      intro w hw
      have h : (⟨((e (π w) : D) : V), hπmem w⟩ : Sb) = ⟨((e w : D) : V), hw⟩ :=
        Subtype.ext (by simp only [hπW w hw])
      show e.symm (incl (LQ ⟨((e (π w) : D) : V), hπmem w⟩)) = _
      rw [h]
    have hcomm : TP ∘ₗ LQ = LQ ∘ₗ TP := by
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ((TP (LQ x) : Sb) : V) = ((LQ (TP x) : Sb) : V)
      have hx : e.symm (incl x) ∈ W := by rw [hWmem]; simp [incl]
      have hgx : g (e.symm (incl x)) = e.symm (incl (LQ x)) := by
        rw [hg _ hx]; congr 3
      have hgP : g (P (e.symm (incl x))) = e.symm (incl (LQ (TP x))) := by
        rw [hg _ (hPW _ hx)]; congr 3
      rw [hTP, ← hgx, hPc g, hgP, LinearEquiv.apply_symm_apply]
      rfl
    have hmQ : LinearMap.toMatrix Bs Bs LQ = Q := LinearMap.toMatrix_toLin Bs Bs Q
    rw [← hmQ, ← LinearMap.toMatrix_comp Bs Bs Bs, hcomm, LinearMap.toMatrix_comp Bs Bs Bs]

  have hstarA : ∀ k ∈ K, star Pm * A k = A k * star Pm := by
    intro k hk
    have hu1 : A k * star (A k) = 1 := Matrix.mem_unitaryGroup_iff.1 (hU k hk)
    have hu2 : star (A k) * A k = 1 := Matrix.mem_unitaryGroup_iff'.1 (hU k hk)
    have hs : star (A k) * star Pm = star Pm * star (A k) := by
      rw [← star_mul, ← star_mul, hcommA k hk]
    calc star Pm * A k = (A k * star (A k)) * star Pm * A k := by rw [hu1, one_mul]
      _ = A k * (star (A k) * star Pm) * A k := by simp only [mul_assoc]
      _ = A k * (star Pm * star (A k)) * A k := by rw [hs]
      _ = A k * star Pm * (star (A k) * A k) := by simp only [mul_assoc]
      _ = A k * star Pm := by rw [hu2, mul_one]
  have hnorm : Pm * star Pm = star Pm * Pm := hcommQ (star Pm) hstarA
  have hss' : star Pm * star Pm = star Pm := by rw [← star_mul, hidem]
  set N := Pm - star Pm * Pm with hN
  have hNs : star N = star Pm - star Pm * Pm := by
    rw [hN, star_sub, star_mul, star_star]
  have hNN : star N * N = 0 := by
    rw [hNs, hN]
    have e1 : star Pm * Pm * Pm = star Pm * Pm := by rw [mul_assoc, hidem]
    have e2 : star Pm * (star Pm * Pm) = star Pm * Pm := by rw [← mul_assoc, hss']
    have e3 : star Pm * Pm * (star Pm * Pm) = star Pm * Pm := by
      calc star Pm * Pm * (star Pm * Pm) = star Pm * (Pm * star Pm) * Pm := by simp only [mul_assoc]
        _ = star Pm * (star Pm * Pm) * Pm := by rw [hnorm]
        _ = star Pm * Pm := by rw [e2, e1]
    rw [sub_mul, mul_sub, mul_sub, e1, e2, e3]
    abel
  have hN0 : N = 0 := by
    rw [Matrix.star_eq_conjTranspose] at hNN
    open scoped ComplexOrder in exact Matrix.conjTranspose_mul_self_eq_zero.1 hNN
  have hPm : Pm = star Pm * Pm := sub_eq_zero.1 (hN ▸ hN0)
  refine ⟨Pm, hform, ?_⟩
  calc star Pm = star (star Pm * Pm) := by rw [← hPm]
    _ = star Pm * Pm := by rw [star_mul, star_star]
    _ = Pm := hPm.symm
