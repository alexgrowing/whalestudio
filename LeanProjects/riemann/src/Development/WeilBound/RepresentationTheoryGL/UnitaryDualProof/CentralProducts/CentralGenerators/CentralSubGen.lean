import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.CS

variable {k : Type} [Field k]

theorem sc_one (n : ℕ) : sc n (1 : kˣ) = 1 := map_one _

theorem sc_mul (n : ℕ) (y z : kˣ) : sc n (y * z) = sc n y * sc n z := map_mul _ _ _

theorem sc_comm (n : ℕ) (y : kˣ) (g : GL (Fin n) k) : sc n y * g = g * sc n y := by
  apply Units.ext
  have h : ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.scalar (Fin n) (y : k) := rfl
  show ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) =
    (g : Matrix (Fin n) (Fin n) k) * ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  rw [h]
  exact (Matrix.scalar_commute (y : k) (fun r => Commute.all _ _) _).eq

theorem rho_sc_comm {n : ℕ} (A : GRep k n) (y : kˣ) (g : GL (Fin n) k) (v : A.V) :
    A.ρ (sc n y) (A.ρ g v) = A.ρ g (A.ρ (sc n y) v) := by
  rw [← Module.End.mul_apply, ← map_mul, sc_comm, map_mul, Module.End.mul_apply]

theorem centralSub_gen [TopologicalSpace k] : CentralSub k := by
  classical
  intro n A _hs hLF x c a ha hxa
  obtain ⟨U, hUf, haU, hUinv⟩ := hLF a
  have := hUf
  let Good : Submodule ℂ A.V → Prop := fun S => S ≤ U ∧ S ≠ ⊥ ∧
    (∀ y : kˣ, ∀ s ∈ S, A.ρ (sc n y) s ∈ S) ∧ ∀ s ∈ S, A.ρ (sc n x) s = c • s
  have hex : ∃ d : ℕ, ∃ S : Submodule ℂ A.V, Good S ∧ Module.finrank ℂ S = d := by
    refine ⟨_, U ⊓ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id), ⟨inf_le_left, ?_, ?_, ?_⟩, rfl⟩
    · intro h
      apply ha
      have hm : a ∈ U ⊓ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id) :=
        ⟨haU, by simp [LinearMap.mem_ker, hxa]⟩
      rw [h] at hm
      exact (Submodule.mem_bot ℂ).1 hm
    · rintro y s ⟨hsU, hsk⟩
      refine ⟨hUinv y s hsU, ?_⟩
      have hsk' : A.ρ (sc n x) s = c • s := by
        simpa [LinearMap.mem_ker, sub_eq_zero] using hsk
      show A.ρ (sc n y) s ∈ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, rho_sc_comm A x (sc n y) s, hsk', map_smul]
      simp
    · rintro s ⟨_, hsk⟩
      simpa [LinearMap.mem_ker, sub_eq_zero] using hsk
  obtain ⟨S, ⟨hSU, hS0, hSinv, hSx⟩, hSd⟩ := Nat.find_spec hex
  have hmin : ∀ S' : Submodule ℂ A.V, Good S' → Module.finrank ℂ S ≤ Module.finrank ℂ S' := by
    intro S' hS'
    rw [hSd]
    exact Nat.find_min' hex ⟨S', hS', rfl⟩
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  have hscal : ∀ y : kˣ, ∃ μ : ℂ, ∀ s ∈ S, A.ρ (sc n y) s = μ • s := by
    intro y
    let f : Module.End ℂ S := (A.ρ (sc n y)).restrict (hSinv y)
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    refine ⟨μ, ?_⟩
    have hfw : A.ρ (sc n y) (w : A.V) = μ • (w : A.V) := congrArg Subtype.val hw.apply_eq_smul
    let S' : Submodule ℂ A.V := S ⊓ LinearMap.ker (A.ρ (sc n y) - μ • LinearMap.id)
    have hmem : ∀ s, s ∈ S' ↔ s ∈ S ∧ A.ρ (sc n y) s = μ • s := by
      intro s
      simp [S', Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hgood : Good S' := by
      refine ⟨inf_le_left.trans hSU, ?_, ?_, ?_⟩
      · intro h
        have hw' : (w : A.V) ∈ S' := (hmem _).2 ⟨w.2, hfw⟩
        rw [h] at hw'
        exact hw.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hw'))
      · intro y' s hs
        obtain ⟨hsS, hsy⟩ := (hmem s).1 hs
        refine (hmem _).2 ⟨hSinv y' s hsS, ?_⟩
        rw [rho_sc_comm A y (sc n y') s, hsy, map_smul]
      · intro s hs
        exact hSx s ((hmem s).1 hs).1
    have hEq : S' = S := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin S' hgood)
    intro s hs
    rw [← hEq] at hs
    exact ((hmem s).1 hs).2
  choose lam hlam using hscal
  obtain ⟨a', ha'S, ha'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have key : ∀ μ ν : ℂ, μ • a' = ν • a' → μ = ν := fun μ ν h => smul_left_injective ℂ ha'0 h
  have hlam1 : lam 1 = 1 := by
    apply key
    rw [← hlam 1 a' ha'S, sc_one, map_one, Module.End.one_apply, one_smul]
  have hlammul : ∀ y z : kˣ, lam (y * z) = lam y * lam z := by
    intro y z
    apply key
    rw [← hlam (y * z) a' ha'S, sc_mul, map_mul, Module.End.mul_apply, hlam z a' ha'S, map_smul,
      hlam y a' ha'S, smul_smul, mul_comm]
  let f : kˣ →* ℂ := { toFun := lam, map_one' := hlam1, map_mul' := hlammul }
  let Wm : Submodule ℂ A.V :=
    { carrier := {v | ∀ y : kˣ, A.ρ (sc n y) v = lam y • v}
      add_mem' := by
        intro u v hu hv y
        have hu' : ∀ y : kˣ, A.ρ (sc n y) u = lam y • u := hu
        have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
        show A.ρ (sc n y) (u + v) = lam y • (u + v)
        rw [map_add, hu' y, hv' y, smul_add]
      zero_mem' := by
        intro y
        show A.ρ (sc n y) 0 = lam y • (0 : A.V)
        rw [map_zero, smul_zero]
      smul_mem' := by
        intro r v hv y
        have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
        show A.ρ (sc n y) (r • v) = lam y • (r • v)
        rw [map_smul, hv' y, smul_comm] }
  let W : Subrepresentation A.ρ := ⟨Wm, fun g v hv y => by
    have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
    show A.ρ (sc n y) (A.ρ g v) = lam y • A.ρ g v
    rw [rho_sc_comm, hv' y, map_smul]⟩
  have ha'W : a' ∈ W.toSubmodule := fun y => hlam y a' ha'S
  refine ⟨W, f.toHomUnits, ?_, ?_, ?_⟩
  · intro h
    apply ha'0
    have h2 : W.toSubmodule = (⊥ : Subrepresentation A.ρ).toSubmodule := congrArg _ h
    have h3 : a' ∈ (⊥ : Subrepresentation A.ρ).toSubmodule := h2 ▸ ha'W
    exact (Submodule.mem_bot ℂ).1 h3
  · intro z v
    apply Subtype.ext
    show A.ρ (sc n z) v.1 = ((f.toHomUnits z : ℂˣ) : ℂ) • v.1
    rw [MonoidHom.coe_toHomUnits]
    exact v.2 z
  · show ((f.toHomUnits x : ℂˣ) : ℂ) = c
    rw [MonoidHom.coe_toHomUnits]
    exact (key _ _ ((hlam x a' ha'S).symm.trans (hSx a' ha'S))).trans rfl

theorem centralSub (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CentralSub k :=
  centralSub_gen

end PositivityTheory.RgUd.Prod.CS
